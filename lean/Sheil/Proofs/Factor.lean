/- Sheil/Proofs/Factor.lean — proofs of the row lem_2_2_factor of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Proofs.Basic

namespace Sheil.Proofs

open Polynomial ComplexConjugate

lemma pstar_linear (root : ℂ) : pstar 1 (X - C root) = 1 - C (conj root) * X := by
  simp [pstar, Finset.sum_range_succ]
  <;> ring

theorem lem_2_2_factor_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n)
    (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0) :
    ∃ beta : Fin n → ℂ, (∀ l, ‖beta l‖ ≤ 1) ∧
      (∀ z : ℂ, H.eval z = H.coeff 0 * ∏ l, (1 - conj (beta l) * z)) ∧
      (∀ z : ℂ, (pstar n H).eval z = conj (H.coeff 0) * ∏ l, (z - beta l)) := by
  classical
  induction n generalizing H with
  | zero =>
    have hc : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdeg)
    refine ⟨Fin.elim0, by simp, ?_, ?_⟩
    · intro z; simpa using congrArg (fun p : ℂ[X] => p.eval z) hc
    · intro z; simp [pstar]
  | succ n ih =>
    by_cases hconst : H.natDegree = 0
    · have hc : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero hconst
      refine ⟨fun _ => 0, by simp, ?_, ?_⟩
      · intro z; simpa using congrArg (fun p : ℂ[X] => p.eval z) hc
      · intro z
        rw [pstar_eq_reflect_map _ _ hdeg, hc, reflect_C]
        simp
    · have hzero : H.coeff 0 ≠ 0 := by
        simpa only [coeff_zero_eq_eval_zero] using hD 0 (by simp [unitDisc])
      have hH : H ≠ 0 := by intro h; simp [h] at hzero
      obtain ⟨root, hroot⟩ := IsAlgClosed.exists_root H
        (by intro hd; exact hconst (natDegree_eq_of_degree_eq_some hd))
      obtain ⟨Q, hfac⟩ := (dvd_iff_isRoot.mpr hroot)
      have hQ : Q ≠ 0 := by intro h; simp [h] at hfac; exact hH hfac
      have hdQ : Q.natDegree ≤ n := by
        rw [hfac, natDegree_mul (X_sub_C_ne_zero root) hQ, natDegree_X_sub_C] at hdeg
        omega
      have hDQ : ∀ z ∈ unitDisc, Q.eval z ≠ 0 := by
        intro z hz hq
        apply hD z hz
        simp [hfac, hq]
      have hr : 1 ≤ ‖root‖ := by
        by_contra hs
        exact hD root (by simpa [unitDisc, Metric.mem_ball, dist_zero_right] using lt_of_not_ge hs) hroot
      have hr0 : root ≠ 0 := by intro h; norm_num [h] at hr
      have hcr0 : conj root ≠ 0 := by simpa using hr0
      have hc0 : H.coeff 0 = -root * Q.coeff 0 := by
        simpa [coeff_zero_eq_eval_zero] using congrArg (fun p : ℂ[X] => p.eval 0) hfac
      obtain ⟨beta, hbeta, heval, hstar⟩ := ih Q hdQ hDQ
      refine ⟨Fin.cons (conj root)⁻¹ beta, ?_, ?_, ?_⟩
      · intro l
        refine Fin.cases ?_ (fun k => ?_) l
        · simp only [Fin.cons_zero, norm_inv, RCLike.norm_conj]
          exact inv_le_one_of_one_le₀ hr
        · simpa using hbeta k
      · intro z
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hc0, hfac, eval_mul, eval_sub, eval_X, eval_C, heval z]
        have hconj : conj ((conj root)⁻¹) = root⁻¹ := by simp
        rw [hconj]
        field_simp [hr0]
        <;> ring
      · intro z
        have hps : pstar (n + 1) H = pstar 1 (X - C root) * pstar n Q := by
          rw [hfac, Nat.add_comm n 1, pstar_mul 1 n _ _ (by simp) hdQ]
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hps, eval_mul, pstar_linear, eval_sub, eval_one, eval_mul, eval_C, eval_X, hstar z, hc0]
        simp only [map_mul, map_neg]
        field_simp
        <;> ring

end Sheil.Proofs
