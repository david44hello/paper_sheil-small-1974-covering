/- Sheil/Proofs/GramPSD.lean — proofs of the rows schurCohn_posSemidef, lem_2_2_b of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Proofs.SchurIdentity
import Sheil.Proofs.Factor
import Sheil.Proofs.GramExpansion

namespace Sheil.Proofs

open Polynomial ComplexConjugate
open scoped ComplexOrder

noncomputable def polyGramMatrix (n : ℕ) (family : Fin n → ℂ[X]) (weight : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ l, weight l • Matrix.vecMulVec (fun i : Fin n => (family l).coeff i)
    (star (fun i : Fin n => (family l).coeff i))

lemma polyGramMatrix_apply (n : ℕ) (family : Fin n → ℂ[X]) (weight : Fin n → ℝ) (i j : Fin n) :
    polyGramMatrix n family weight i j =
      ∑ l, (weight l : ℂ) * (family l).coeff i * conj ((family l).coeff j) := by
  simp [polyGramMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Complex.real_smul, mul_assoc]

lemma polyGramMatrix_posSemidef (n : ℕ) (family : Fin n → ℂ[X]) (weight : Fin n → ℝ)
    (hw : ∀ l, 0 ≤ weight l) : (polyGramMatrix n family weight).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro l hl
  exact (Matrix.posSemidef_vecMulVec_self_star (fun i : Fin n => (family l).coeff i)).smul (hw l)

lemma eval_fin_coeff (n : ℕ) (F : ℂ[X]) (hdeg : F.natDegree < n) (z : ℂ) :
    F.eval z = ∑ i : Fin n, F.coeff i * z ^ (i : ℕ) := by
  rw [eval_eq_sum_range' hdeg z, Finset.sum_range]

lemma sum_rotate {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] (f : a → b → c → ℂ) :
    (∑ i, ∑ j, ∑ l, f i j l) = ∑ l, ∑ i, ∑ j, f i j l := by
  calc
    (∑ i, ∑ j, ∑ l, f i j l) = ∑ i, ∑ l, ∑ j, f i j l := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma polyGramMatrix_form (n : ℕ) (family : Fin n → ℂ[X]) (weight : Fin n → ℝ)
    (hdeg : ∀ l, (family l).natDegree < n) (z eta : ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, polyGramMatrix n family weight i j * z ^ (i : ℕ) * conj eta ^ (j : ℕ)) =
      ∑ l, (weight l : ℂ) * (family l).eval z * conj ((family l).eval eta) := by
  simp_rw [polyGramMatrix_apply, Finset.sum_mul]
  rw [sum_rotate]
  apply Finset.sum_congr rfl
  intro l hl
  rw [eval_fin_coeff n (family l) (hdeg l) z, eval_fin_coeff n (family l) (hdeg l) eta]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem schurCohn_psd_of_gram (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n)
    (family : Fin n → ℂ[X]) (weight : Fin n → ℝ) (hw : ∀ l, 0 ≤ weight l)
    (hf : ∀ l, (family l).natDegree < n)
    (hkernel : ∀ z eta : ℂ,
      H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta) =
        (1 - z * conj eta) * ∑ l, (weight l : ℂ) * (family l).eval z * conj ((family l).eval eta)) :
    (schurCohn n H).PosSemidef := by
  have hK : polyGramMatrix n family weight = schurCohn n H := by
    apply schurCohn_unique_proved n H hdeg
    intro z eta
    rw [polyGramMatrix_form n family weight hf z eta]
    exact (hkernel z eta).symm
  rw [← hK]
  exact polyGramMatrix_posSemidef n family weight hw

theorem schurCohn_posSemidef_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n)
    (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0) : (schurCohn n H).PosSemidef := by
  obtain ⟨beta, hbeta, heval, hstar⟩ := lem_2_2_factor_proved n H hdeg hD
  obtain ⟨family, weight, hw, hf, hkernel⟩ := factor_gram_expansion n beta hbeta
  apply schurCohn_psd_of_gram n H hdeg family (fun l => ‖H.coeff 0‖ ^ 2 * weight l)
  · intro l
    exact mul_nonneg (sq_nonneg _) (hw l)
  · exact hf
  · intro z eta
    have hscale :
        (∑ l, ((‖H.coeff 0‖ ^ 2 * weight l : ℝ) : ℂ) *
          (family l).eval z * conj ((family l).eval eta)) =
        ((‖H.coeff 0‖ ^ 2 : ℝ) : ℂ) *
          ∑ l, (weight l : ℂ) * (family l).eval z * conj ((family l).eval eta) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      push_cast
      ring
    rw [heval z, heval eta, hstar z, hstar eta, hscale]
    simp only [map_mul, Complex.conj_conj]
    have hs := congrArg (fun v : ℂ => ((‖H.coeff 0‖ ^ 2 : ℝ) : ℂ) * v) (hkernel z eta)
    have hnorm : ((‖H.coeff 0‖ ^ 2 : ℝ) : ℂ) = H.coeff 0 * conj (H.coeff 0) := by
      push_cast
      exact (Complex.mul_conj' _).symm
    rw [hnorm] at hs
    rw [hnorm]
    linear_combination hs

theorem lem_2_2_b_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n)
    (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0) :
    (∀ z eta : ℂ, (1 - z * conj eta) * schurCohnForm n H z eta =
      H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta)) ∧
    (∀ z eta : ℂ, z * conj eta ≠ 1 → schurCohnForm n H z eta =
      (H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta)) / (1 - z * conj eta)) ∧
    (schurCohn n H).PosSemidef := by
  refine ⟨schurCohn_identity n H hdeg, ?_, schurCohn_posSemidef_proved n H hdeg hD⟩
  intro z eta hne
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hne))).mpr
  simpa only [mul_comm] using schurCohn_identity n H hdeg z eta

#print axioms lem_2_2_b_proved

end Sheil.Proofs
