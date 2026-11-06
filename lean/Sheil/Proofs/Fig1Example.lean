/- Sheil/Proofs/Fig1Example.lean — proofs of the row fig1_example of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Defs.Examples
import Sheil.Proofs.Rows

namespace Sheil

open Polynomial ComplexConjugate

theorem five_eval (z : ℂ) : polyFive.eval z = 1 + z + 5 * z ^ 2 + z ^ 3 + z ^ 4 := by
  simp [polyFive]

theorem five_natDegree : polyFive.natDegree = 4 := by
  unfold polyFive
  compute_degree!

theorem five_coeff0 : polyFive.coeff 0 = 1 := by simp [polyFive, coeff_one, coeff_X, coeff_X_pow]
theorem five_coeff1 : polyFive.coeff 1 = 1 := by simp [polyFive, coeff_one, coeff_X, coeff_X_pow]
theorem five_coeff2 : polyFive.coeff 2 = 5 := by simp [polyFive, coeff_one, coeff_X, coeff_X_pow]
theorem five_coeff3 : polyFive.coeff 3 = 1 := by simp [polyFive, coeff_one, coeff_X, coeff_X_pow]
theorem five_coeff4 : polyFive.coeff 4 = 1 := by simp [polyFive, coeff_one, coeff_X, coeff_X_pow]

/-- `P* = P`: the coefficients read the same in both directions and are real. -/
theorem five_pstar : pstar 4 polyFive = C 1 * polyFive := by
  have hconj : conj (5 : ℂ) = 5 := map_ofNat _ 5
  ext k
  rw [coeff_pstar, coeff_C_mul]
  split_ifs with hk
  · interval_cases k <;> simp [five_coeff0, five_coeff1, five_coeff2, five_coeff3, five_coeff4, hconj]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [five_natDegree]; omega)]
    simp

theorem five_selfInversive : SelfInversive polyFive := by
  refine ⟨by rw [five_natDegree]; norm_num, 1, by simp, ?_⟩
  rw [five_natDegree]
  exact five_pstar

/-- `A = 5`. -/
theorem five_coefMaxDeg : coefMaxDeg polyFive = 5 := by
  unfold coefMaxDeg
  rw [five_natDegree]
  apply le_antisymm
  · unfold coefMax
    apply Finset.sup'_le
    intro k hk
    have hk5 : k < 5 := Finset.mem_range.mp hk
    interval_cases k
    · rw [five_coeff0]; norm_num
    · rw [five_coeff1]; norm_num
    · rw [five_coeff2]; norm_num
    · rw [five_coeff3]; norm_num
    · rw [five_coeff4]; norm_num
  · have h := le_coefMax (n := 4) (k := 2) polyFive (by norm_num)
    rw [five_coeff2] at h
    simpa using h

/-- On `|z| = 1` we have `|5z^2| = 5 > 4 ≥ |1 + z + z^3 + z^4|`, so `P` has no zero there. -/
theorem five_zero_off_circle (z : ℂ) (hz : polyFive.IsRoot z) : ‖z‖ ≠ 1 := by
  intro hnorm
  have hzero : 1 + z + 5 * z ^ 2 + z ^ 3 + z ^ 4 = 0 := by
    rw [← five_eval]
    exact hz
  have hmiddle : 5 * z ^ 2 = -(1 + z + z ^ 3 + z ^ 4) := by linear_combination hzero
  have hleft : ‖5 * z ^ 2‖ = 5 := by simp [hnorm]
  have hright : ‖1 + z + z ^ 3 + z ^ 4‖ ≤ 4 := by
    calc ‖1 + z + z ^ 3 + z ^ 4‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ + ‖z ^ 3‖ + ‖z ^ 4‖ := norm_add₄_le
      _ = 4 := by simp [hnorm]; norm_num
  rw [hmiddle, norm_neg] at hleft
  linarith

/-- Row `fig1_example`; the disc comes from Theorem 4.1 (the hypothesis `hthm`). -/
theorem fig1_example_of (hthm : HypThm41) :
    SelfInversive polyFive ∧ coefMaxDeg polyFive = 5 ∧ (∀ z : ℂ, polyFive.IsRoot z → ‖z‖ ≠ 1) ∧
      ∃ c : ℂ, Metric.ball c 5 ⊆ discImage polyFive := by
  refine ⟨five_selfInversive, five_coefMaxDeg, five_zero_off_circle, ?_⟩
  have hdisc := abs_self_inversive_of hthm polyFive five_selfInversive
  rwa [five_coefMaxDeg] at hdisc

#print axioms fig1_example_of

end Sheil
