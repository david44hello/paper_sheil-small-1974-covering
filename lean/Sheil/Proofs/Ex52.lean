/- Sheil/Proofs/Ex52.lean — proofs of the rows ex_5_2 of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Mathlib
import Sheil.Defs.Basic
import Sheil.Defs.Examples
import Sheil.Proofs.Sec4

namespace Sheil

open Polynomial ComplexConjugate
open scoped ComplexOrder

/-! ### Evaluation and coefficients -/

theorem ex52_eval (a : ℝ) (m : ℕ) (z : ℂ) :
    (polyLimacon a m).eval z = 1 + (a : ℂ) * z ^ m + (z ^ m) ^ 2 := by
  simp only [polyLimacon, eval_add, eval_one, eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem ex52_coeff (a : ℝ) (m k : ℕ) : (polyLimacon a m).coeff k =
    (if k = 0 then 1 else 0) + (if k = m then (a : ℂ) else 0) + (if k = 2 * m then 1 else 0) := by
  simp only [polyLimacon, coeff_add, coeff_one, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]

theorem ex52_coeff_zero (a : ℝ) {m : ℕ} (hm : 1 ≤ m) : (polyLimacon a m).coeff 0 = 1 := by
  rw [ex52_coeff, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]
  ring

theorem ex52_coeff_mid (a : ℝ) {m : ℕ} (hm : 1 ≤ m) : (polyLimacon a m).coeff m = a := by
  rw [ex52_coeff, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega)]
  ring

theorem ex52_coeff_two (a : ℝ) {m : ℕ} (hm : 1 ≤ m) : (polyLimacon a m).coeff (2 * m) = 1 := by
  rw [ex52_coeff, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  ring

theorem ex52_coeff_other (a : ℝ) {m k : ℕ} (h0 : k ≠ 0) (h1 : k ≠ m) (h2 : k ≠ 2 * m) :
    (polyLimacon a m).coeff k = 0 := by
  rw [ex52_coeff, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
  ring

theorem ex52_natDegree (a : ℝ) {m : ℕ} (hm : 1 ≤ m) : (polyLimacon a m).natDegree = 2 * m := by
  unfold polyLimacon
  have h1 : (1 + C (a : ℂ) * X ^ m : ℂ[X]).natDegree ≤ m :=
    (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_C_mul_X_pow_le _ _))
  have h2 : (X ^ (2 * m) : ℂ[X]).natDegree = 2 * m := natDegree_X_pow _
  rw [natDegree_add_eq_right_of_natDegree_lt (h1.trans_lt (by rw [h2]; omega)), h2]

theorem ex52_mirror (a : ℝ) {m : ℕ} (hm : 1 ≤ m) : Mirror (2 * m) (polyLimacon a m) := by
  intro k hk
  by_cases h0 : k = 0
  · subst h0
    rw [Nat.sub_zero, ex52_coeff_zero a hm, ex52_coeff_two a hm]
  by_cases h1 : k = m
  · subst h1
    rw [show 2 * k - k = k by omega]
  by_cases h2 : k = 2 * m
  · subst h2
    rw [Nat.sub_self, ex52_coeff_zero a hm, ex52_coeff_two a hm]
  rw [ex52_coeff_other a h0 h1 h2, ex52_coeff_other a (by omega) (by omega) (by omega)]

theorem ex52_norm_a {a : ℝ} (ha : 4 ≤ a) : ‖(a : ℂ)‖ = a := Complex.norm_of_nonneg (by linarith)

theorem ex52_norm_coeff_le {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    ‖(polyLimacon a m).coeff k‖ ≤ a := by
  by_cases h0 : k = 0
  · subst h0
    rw [ex52_coeff_zero a hm, norm_one]; linarith
  by_cases h1 : k = m
  · subst h1
    rw [ex52_coeff_mid a hm, ex52_norm_a ha]
  by_cases h2 : k = 2 * m
  · subst h2
    rw [ex52_coeff_two a hm, norm_one]; linarith
  rw [ex52_coeff_other a h0 h1 h2, norm_zero]; linarith

theorem ex52_coefMax {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) : coefMax (2 * m) (polyLimacon a m) = a := by
  apply le_antisymm
  · unfold coefMax
    exact Finset.sup'_le _ _ (fun k _ => ex52_norm_coeff_le ha hm k)
  · have h := le_coefMax (n := 2 * m) (k := m) (polyLimacon a m) (by omega)
    rwa [ex52_coeff_mid a hm, ex52_norm_a ha] at h

theorem ex52_coefMaxDeg {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) : coefMaxDeg (polyLimacon a m) = a := by
  unfold coefMaxDeg
  rw [ex52_natDegree a hm, ex52_coefMax ha hm]

theorem ex52_ratio {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    (polyLimacon a m).coeff (2 * m - m) / conj ((polyLimacon a m).coeff m) = 1 := by
  rw [show 2 * m - m = m by omega, ex52_coeff_mid a hm, Complex.conj_ofReal]
  exact div_self (Complex.ofReal_ne_zero.mpr (by linarith))

/-! ### The circle formula and the real inequalities -/

theorem ex52_circle (a : ℝ) (m : ℕ) (z : ℂ) (θ : ℝ) (hz : z ^ m = Complex.exp (θ * Complex.I)) :
    (polyLimacon a m).eval z = Complex.exp (θ * Complex.I) * ((a : ℂ) + 2 * Real.cos θ) ∧
      ((polyLimacon a m).eval z).re = a * Real.cos θ + 2 * Real.cos θ ^ 2 := by
  have heval : (polyLimacon a m).eval z = Complex.exp (θ * Complex.I) * ((a : ℂ) + 2 * Real.cos θ) := by
    rw [ex52_eval, hz, Complex.ofReal_cos, Complex.exp_mul_I]
    linear_combination (-1 : ℂ) * Complex.sin_sq_add_cos_sq (θ : ℂ) +
      Complex.sin (θ : ℂ) ^ 2 * Complex.I_sq
  refine ⟨heval, ?_⟩
  have hr : (a : ℂ) + 2 * (Real.cos θ : ℂ) = ((a + 2 * Real.cos θ : ℝ) : ℂ) := by push_cast; ring
  rw [heval, hr, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  ring

theorem ex52_deriv (a x : ℝ) : HasDerivAt (fun y : ℝ => a * y + 2 * y ^ 2) (a + 4 * x) x := by
  have h := ((hasDerivAt_id' x).const_mul a).add ((hasDerivAt_pow 2 x).const_mul 2)
  convert h using 1
  norm_num
  ring

theorem ex52_real_ineq {a : ℝ} (ha : 4 ≤ a) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => a * y + 2 * y ^ 2) (a + 4 * x) x ∧ 0 ≤ a + 4 * x ∧
      2 - a ≤ a * x + 2 * x ^ 2 ∧ a * x + 2 * x ^ 2 ≤ 2 + a := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨ex52_deriv a x, by linarith, ?_, ?_⟩
  · nlinarith [mul_nonneg (show 0 ≤ x + 1 by linarith) (show 0 ≤ a + 2 * x - 2 by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ a + 2 + 2 * x by linarith)]

/-! ### The vertical strip `2 - a < Re w < 2 + a` and the radius bound -/

theorem ex52_strip {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    ∀ w ∈ discImage (polyLimacon a m), 2 - a < w.re ∧ w.re < 2 + a := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := mem_discImage.mp hw
  set ζ := z ^ m with hζ
  have hζ1 : ‖ζ‖ < 1 := by
    rw [hζ, norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hz (by omega)
  have hsq : ζ.re * ζ.re + ζ.im * ζ.im < 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm]
    exact pow_lt_one₀ (norm_nonneg ζ) hζ1 (by norm_num)
  have hre : ((polyLimacon a m).eval z).re = 1 + a * ζ.re + ζ.re ^ 2 - ζ.im ^ 2 := by
    rw [ex52_eval, ← hζ]
    simp [pow_two]
    ring
  rw [hre]
  have hu1 : ζ.re < 1 := by nlinarith [mul_self_nonneg ζ.im, sq_nonneg (ζ.re - 1)]
  have hu2 : -1 < ζ.re := by nlinarith [mul_self_nonneg ζ.im, sq_nonneg (ζ.re + 1)]
  constructor
  · nlinarith [mul_pos (show 0 < 1 + ζ.re by linarith) (show 0 < a + 2 * ζ.re - 2 by linarith)]
  · nlinarith [mul_pos (show 0 < 1 - ζ.re by linarith) (show 0 < 1 + ζ.re + a by linarith),
      sq_nonneg ζ.im]

theorem ex52_radius {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    ∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage (polyLimacon a m) → r ≤ a := by
  intro c r hball
  by_contra hr
  push Not at hr
  have hp : c + (a : ℂ) ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, ex52_norm_a ha]; exact hr
  have hn : c - (a : ℂ) ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, ex52_norm_a ha]; exact hr
  have h1 := (ex52_strip ha hm _ (hball hp)).2
  have h2 := (ex52_strip ha hm _ (hball hn)).1
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h1 h2
  linarith

/-! ### A zero in the disc, and the covering disc `D(2, a)` -/

theorem ex52_zero {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    ∃ z ∈ unitDisc, (polyLimacon a m).eval z = 0 := by
  set s := Real.sqrt (a ^ 2 - 4) with hsdef
  have hs : s ^ 2 = a ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set ζ0 : ℝ := (-a + s) / 2 with hζ0
  have hroot : 1 + a * ζ0 + ζ0 ^ 2 = 0 := by rw [hζ0]; linear_combination (1 / 4 : ℝ) * hs
  have hlt : s < a := by nlinarith
  have hgt : a - 2 < s := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ a - 2 by linarith) (show (0 : ℝ) ≤ a - 2 by linarith)]
  have habs : |ζ0| < 1 := by rw [abs_lt]; constructor <;> linarith
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((ζ0 : ℝ) : ℂ) (show 0 < m by omega)
  have hzlt : ‖z‖ < 1 := by
    by_contra hge
    push Not at hge
    have h1 : 1 ≤ ‖z‖ ^ m := one_le_pow₀ hge
    rw [← norm_pow, hz, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith
  refine ⟨z, ?_, ?_⟩
  · simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hzlt
  · rw [ex52_eval, hz]
    exact_mod_cast hroot

theorem ex52_ball (hPSD : HypPSD) {a : ℝ} (ha : 4 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    Metric.ball 2 a ⊆ discImage (polyLimacon a m) := by
  have hcm := ex52_coefMax ha hm
  have hw : 1 - (polyLimacon a m).coeff (2 * m - m) / conj ((polyLimacon a m).coeff m) ∈
      discImage (polyLimacon a m) := by
    rw [ex52_ratio ha hm, sub_self]
    obtain ⟨z, hz, hz0⟩ := ex52_zero ha hm
    exact ⟨z, hz, hz0⟩
  have hjA : ‖(polyLimacon a m).coeff m‖ = coefMax (2 * m) (polyLimacon a m) := by
    rw [ex52_coeff_mid a hm, ex52_norm_a ha, hcm]
  have h := rem_4_2_wstar_taken_of hPSD (2 * m) (by omega) (polyLimacon a m)
    (ex52_natDegree a hm).le (ex52_mirror a hm) (ex52_coeff_zero a hm) (ex52_coeff_two a hm)
    (by rw [hcm]; linarith) m hm (by omega) hjA hw
  rw [ex52_ratio ha hm, hcm, show (1 : ℂ) + 1 = 2 by norm_num] at h
  exact h

/-! ### Row `ex_5_2` -/

theorem ex_5_2_of (hPSD : HypPSD) (a : ℝ) (ha : 4 ≤ a) (m : ℕ) (hm : 1 ≤ m) :
    (∀ z : ℂ, ∀ θ : ℝ, z ^ m = Complex.exp (θ * Complex.I) →
      (polyLimacon a m).eval z = Complex.exp (θ * Complex.I) * ((a : ℂ) + 2 * Real.cos θ) ∧
      ((polyLimacon a m).eval z).re = a * Real.cos θ + 2 * Real.cos θ ^ 2) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt (fun y : ℝ => a * y + 2 * y ^ 2) (a + 4 * x) x ∧ 0 ≤ a + 4 * x ∧
      2 - a ≤ a * x + 2 * x ^ 2 ∧ a * x + 2 * x ^ 2 ≤ 2 + a) ∧
    (∀ w ∈ discImage (polyLimacon a m), 2 - a < w.re ∧ w.re < 2 + a) ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage (polyLimacon a m) → r ≤ a) ∧
    (polyLimacon a m).natDegree = 2 * m ∧ Mirror (2 * m) (polyLimacon a m) ∧
    coefMaxDeg (polyLimacon a m) = a ∧
    (polyLimacon a m).coeff (2 * m - m) / conj ((polyLimacon a m).coeff m) = 1 ∧
    Metric.ball 2 a ⊆ discImage (polyLimacon a m) ∧
    (∃ z ∈ unitDisc, (polyLimacon a m).eval z = 0) :=
  ⟨fun z θ hz => ex52_circle a m z θ hz, fun x hx => ex52_real_ineq ha x hx, ex52_strip ha hm,
    ex52_radius ha hm, ex52_natDegree a hm, ex52_mirror a hm, ex52_coefMaxDeg ha hm, ex52_ratio ha hm,
    ex52_ball hPSD ha hm, ex52_zero ha hm⟩

end Sheil

#print axioms Sheil.ex_5_2_of
