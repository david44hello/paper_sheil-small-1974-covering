/- Sheil/Proofs/GramExpansion.lean — lemmas used by the proofs.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Proofs.Lemma22

namespace Sheil.Proofs

open Polynomial ComplexConjugate

/-- `∏_l (1 - conj(β_l) X)`, the head polynomial of the expansion step. -/
noncomputable def gramReversedProd {n : ℕ} (beta : Fin n → ℂ) : ℂ[X] :=
  ∏ l, (1 - C (conj (beta l)) * X)

lemma gramReversedProd_eval {n : ℕ} (beta : Fin n → ℂ) (z : ℂ) :
    (gramReversedProd beta).eval z = ∏ l, (1 - conj (beta l) * z) := by
  simp [gramReversedProd, eval_prod]

lemma natDegree_one_sub_C_mul_X_le (a : ℂ) : (1 - C a * X).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans
    (max_le (by rw [natDegree_one]; exact Nat.zero_le 1) (natDegree_C_mul_le a X |>.trans natDegree_X_le))

/- The three steps below are separate term-mode lemmas on purpose: a single tactic proof
(`unfold` + `natDegree_prod_le` + `calc`) elaborated but was rejected by the kernel with
"declaration has metavariables" (logs gram_expansion_01/02). -/
lemma gramReversedProd_natDegree_le_sum {n : ℕ} (beta : Fin n → ℂ) :
    (gramReversedProd beta).natDegree ≤ ∑ l : Fin n, (1 - C (conj (beta l)) * X).natDegree :=
  natDegree_prod_le Finset.univ (fun l => 1 - C (conj (beta l)) * X)

lemma sum_natDegree_one_sub_le {n : ℕ} (beta : Fin n → ℂ) :
    ∑ l : Fin n, (1 - C (conj (beta l)) * X).natDegree ≤ ∑ _l : Fin n, (1 : ℕ) :=
  Finset.sum_le_sum fun l _ => natDegree_one_sub_C_mul_X_le (conj (beta l))

lemma sum_fin_one_eq (n : ℕ) : ∑ _l : Fin n, (1 : ℕ) = n := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

lemma gramReversedProd_natDegree_le {n : ℕ} (beta : Fin n → ℂ) :
    (gramReversedProd beta).natDegree ≤ n :=
  ((gramReversedProd_natDegree_le_sum beta).trans (sum_natDegree_one_sub_le beta)).trans
    (sum_fin_one_eq n).le

/-- One expansion step: the new successor terms are the old ones times `(z - b)`. -/
lemma gram_succ_sum {n : ℕ} (b : ℂ) (family : Fin n → ℂ[X]) (weight : Fin n → ℝ) (z eta : ℂ) :
    ∑ i, (weight i : ℂ) * ((X - C b) * family i).eval z * conj (((X - C b) * family i).eval eta) =
      (z - b) * (conj eta - conj b) *
        ∑ i, (weight i : ℂ) * (family i).eval z * conj ((family i).eval eta) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval_mul, eval_sub, eval_X, eval_C, map_mul, map_sub]
  ring

theorem factor_gram_expansion (n : ℕ) (beta : Fin n → ℂ)
    (hbeta : ∀ l, ‖beta l‖ ≤ 1) :
    ∃ (family : Fin n → ℂ[X]) (weight : Fin n → ℝ),
      (∀ l, 0 ≤ weight l) ∧
      (∀ l, (family l).natDegree < n) ∧
      ∀ z eta : ℂ,
        (∏ l, (1 - conj (beta l) * z)) * conj (∏ l, (1 - conj (beta l) * eta))
          - (∏ l, (z - beta l)) * conj (∏ l, (eta - beta l))
          = (1 - z * conj eta) *
              ∑ l, (weight l : ℂ) * (family l).eval z * conj ((family l).eval eta) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun l => l.elim0, fun l => l.elim0, fun z eta => by simp⟩
  | succ n ih =>
    obtain ⟨family, weight, hw, hdeg, hid⟩ := ih (fun i => beta i.succ) (fun i => hbeta i.succ)
    refine ⟨(Fin.cons (gramReversedProd fun i => beta i.succ) (fun i => (X - C (beta 0)) * family i) :
        Fin (n + 1) → ℂ[X]),
      (Fin.cons (1 - ‖beta 0‖ ^ 2) weight : Fin (n + 1) → ℝ), ?_, ?_, ?_⟩
    · intro l
      refine Fin.cases ?_ (fun i => ?_) l
      · simp only [Fin.cons_zero, sub_nonneg]
        exact pow_le_one₀ (norm_nonneg _) (hbeta 0)
      · simpa only [Fin.cons_succ] using hw i
    · intro l
      refine Fin.cases ?_ (fun i => ?_) l
      · simp only [Fin.cons_zero]
        exact Nat.lt_succ_of_le (gramReversedProd_natDegree_le _)
      · simp only [Fin.cons_succ]
        have h1 := natDegree_mul_le (p := X - C (beta 0)) (q := family i)
        rw [natDegree_X_sub_C] at h1
        have h2 := hdeg i
        omega
    · intro z eta
      have hone := eq_one_factor_proved (beta 0) z eta
      have htail := hid z eta
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun l => 1 - conj (beta l) * eta),
        Fin.prod_univ_succ, Fin.prod_univ_succ (fun l => eta - beta l), Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, gramReversedProd_eval]
      rw [gram_succ_sum]
      simp only [map_mul, map_sub, map_one, Complex.conj_conj]
      linear_combination
        ((∏ i : Fin n, (1 - conj (beta i.succ) * z)) *
            conj (∏ i : Fin n, (1 - conj (beta i.succ) * eta))) * hone +
          ((z - beta 0) * (conj eta - conj (beta 0))) * htail

#print axioms factor_gram_expansion

end Sheil.Proofs
