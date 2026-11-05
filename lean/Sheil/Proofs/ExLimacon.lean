/- Sheil/Proofs/ExLimacon.lean — proofs of the row fig2_limacon of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Mathlib
import Sheil.Defs.Basic
import Sheil.Defs.Examples
import Sheil.Proofs.Sec4

namespace Sheil

open Polynomial ComplexConjugate
open scoped ComplexOrder

theorem lim_eval (z : ℂ) : polyFour.eval z = 1 + 4 * z + z ^ 2 := by
  simp [polyFour]

/-- (1) The circle formula. -/
theorem lim_circle (ψ : ℝ) : polyFour.eval (Complex.exp (ψ * Complex.I)) =
    ((4 + 2 * Real.cos ψ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I) := by
  rw [lim_eval]
  have hfe : Complex.exp (-(ψ : ℂ) * Complex.I) * Complex.exp (ψ * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hc : ((4 + 2 * Real.cos ψ : ℝ) : ℂ) =
      4 + (Complex.exp (ψ * Complex.I) + Complex.exp (-(ψ : ℂ) * Complex.I)) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat]
    rw [Complex.cos]
    ring
  rw [hc]
  linear_combination -hfe

theorem lim_normSq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- (3) The strip `-2 < Re w < 6` on the image. -/
theorem lim_strip (w : ℂ) (hw : w ∈ discImage polyFour) : -2 < w.re ∧ w.re < 6 := by
  obtain ⟨z, hz, rfl⟩ := mem_discImage.mp hw
  rw [lim_eval]
  have hn := lim_normSq z
  have h1 : z.re ^ 2 + z.im ^ 2 < 1 := by
    rw [← hn]; nlinarith [norm_nonneg z]
  have hre : (1 + 4 * z + z ^ 2).re = 1 + 4 * z.re + z.re ^ 2 - z.im ^ 2 := by
    simp [sq, Complex.mul_re]; ring
  rw [hre]
  constructor
  · nlinarith [sq_nonneg (z.re + 1), sq_nonneg z.im]
  · nlinarith [sq_nonneg z.im, sq_nonneg z.re]

theorem lim_natDegree : polyFour.natDegree = 2 := by
  unfold polyFour
  compute_degree!

theorem lim_coeff0 : polyFour.coeff 0 = 1 := by simp [polyFour, coeff_one, coeff_X, coeff_X_pow]
theorem lim_coeff1 : polyFour.coeff 1 = 4 := by simp [polyFour, coeff_one, coeff_X_pow]
theorem lim_coeff2 : polyFour.coeff 2 = 1 := by simp [polyFour, coeff_one, coeff_X_pow]

/-- (4) `A = 4`. -/
theorem lim_coefMaxDeg : coefMaxDeg polyFour = 4 := by
  unfold coefMaxDeg
  rw [lim_natDegree]
  apply le_antisymm
  · unfold coefMax
    apply Finset.sup'_le
    intro k hk
    have hk3 : k < 3 := Finset.mem_range.mp hk
    interval_cases k
    · rw [lim_coeff0]; norm_num
    · rw [lim_coeff1]; norm_num
    · rw [lim_coeff2]; norm_num
  · have h := le_coefMax (n := 2) (k := 1) polyFour (by norm_num)
    rw [lim_coeff1] at h
    simpa using h

/-- The real-number core of (★): for `a > 0`, `(a-2)^2 + b^2 < 1 ↔ (a^2+b^2)^2 - 10 a^2 + 6 b^2 + 9 < 0`. -/
theorem lim_poly (a b : ℝ) (ha : 0 < a) :
    (a - 2) ^ 2 + b ^ 2 < 1 ↔ (a ^ 2 + b ^ 2) ^ 2 - 10 * a ^ 2 + 6 * b ^ 2 + 9 < 0 := by
  have hT : 0 < a ^ 2 + b ^ 2 + 3 := by positivity
  constructor
  · intro h
    have h4 : a ^ 2 + b ^ 2 + 3 < 4 * a := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr h4) (by positivity : (0 : ℝ) < 4 * a + (a ^ 2 + b ^ 2 + 3))]
  · intro h
    have h4 : a ^ 2 + b ^ 2 + 3 < 4 * a := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul hc hc (by positivity) hT.le]
    nlinarith

/-- With `a = 0` the quartic is positive. -/
theorem lim_poly_re_zero (b : ℝ) : ¬ ((0 ^ 2 + b ^ 2) ^ 2 - 10 * 0 ^ 2 + 6 * b ^ 2 + 9 < (0 : ℝ)) := by
  nlinarith [sq_nonneg b, sq_nonneg (b ^ 2)]

/-- The claim: for `s > 0`, `|x| ≤ s`, `t ≥ 0`, `t^2 = s^2 + 6x + 9`: `u - 6 < 2t ↔ u < 4s` with `u = s^2 - 2x`. -/
theorem lim_claim (s x t : ℝ) (hs : 0 < s) (hx1 : -s ≤ x) (hx2 : x ≤ s) (ht : 0 ≤ t)
    (htt : t ^ 2 = s ^ 2 + 6 * x + 9) : s ^ 2 - 2 * x - 6 < 2 * t ↔ s ^ 2 - 2 * x < 4 * s := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hs2 : 2 ≤ s := by nlinarith
    have hu6 : 6 ≤ s ^ 2 - 2 * x := by nlinarith
    have hsq : (s ^ 2 - 2 * x - 6) ^ 2 < (2 * t) ^ 2 := by
      have h0 : 0 ≤ s ^ 2 - 2 * x - 6 := by linarith
      nlinarith [mul_le_mul h.le h.le h0 (by linarith)]
    nlinarith [mul_le_mul hc hc (by positivity) (by linarith)]
  · intro h
    by_cases hu : s ^ 2 - 2 * x < 6
    · linarith
    · push Not at hu
      have hu0 : 0 ≤ s ^ 2 - 2 * x := by linarith
      have hsq : (s ^ 2 - 2 * x) ^ 2 < (4 * s) ^ 2 := by
        nlinarith [mul_le_mul h.le h.le hu0 (by linarith)]
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul hc hc (by positivity) (by linarith)]

/-- (★) in coordinates: if `v^2 = w + 3`, then `u - 6 - 2t` equals the quartic of `lim_poly` at `(Re v, Im v)`. -/
theorem lim_core (v w : ℂ) (hv : v ^ 2 = w + 3) :
    ‖w‖ ^ 2 - 2 * w.re - 6 - 2 * ‖w + 3‖ =
      (v.re ^ 2 + v.im ^ 2) ^ 2 - 10 * v.re ^ 2 + 6 * v.im ^ 2 + 9 := by
  have hw : w = v ^ 2 - 3 := by rw [hv]; ring
  have h3 : ‖w + 3‖ = v.re ^ 2 + v.im ^ 2 := by rw [← hv, norm_pow, lim_normSq]
  have hre : w.re = v.re ^ 2 - v.im ^ 2 - 3 := by
    rw [hw]; simp [sq, Complex.mul_re]
  have him : w.im = 2 * v.re * v.im := by
    rw [hw]; simp [sq, Complex.mul_im]; ring
  rw [h3, lim_normSq w, hre, him]
  ring

/-- The claim, stated for `w ≠ 0`. -/
theorem lim_claim_w (w : ℂ) (hw : w ≠ 0) :
    ‖w‖ ^ 2 - 2 * w.re - 6 < 2 * ‖w + 3‖ ↔ ‖w‖ ^ 2 < 4 * ‖w‖ + 2 * w.re := by
  have hre3 : (w + 3).re = w.re + 3 := by simp
  have him3 : (w + 3).im = w.im := by simp
  have htt : ‖w + 3‖ ^ 2 = ‖w‖ ^ 2 + 6 * w.re + 9 := by
    rw [lim_normSq, lim_normSq, hre3, him3]; ring
  have hc := lim_claim ‖w‖ w.re ‖w + 3‖ (norm_pos_iff.mpr hw)
    (abs_le.mp (Complex.abs_re_le_norm w)).1 (Complex.re_le_norm w) (norm_nonneg _) htt
  rw [hc]
  constructor <;> intro h <;> linarith

/-- (⊆) of the region lemma. -/
theorem lim_sub (z : ℂ) (hz : ‖z‖ < 1) :
    polyFour.eval z = 0 ∨ ‖polyFour.eval z‖ ^ 2 < 4 * ‖polyFour.eval z‖ + 2 * (polyFour.eval z).re := by
  set w := polyFour.eval z with hwdef
  have hv : (z + 2) ^ 2 = w + 3 := by rw [hwdef, lim_eval]; ring
  have hre : (z + 2).re = z.re + 2 := by simp
  have him : (z + 2).im = z.im := by simp
  have hzre : -‖z‖ ≤ z.re := (abs_le.mp (Complex.abs_re_le_norm z)).1
  have ha : 0 < (z + 2).re := by rw [hre]; linarith
  have hb : ((z + 2).re - 2) ^ 2 + (z + 2).im ^ 2 < 1 := by
    rw [hre, him, add_sub_cancel_right, ← lim_normSq]; nlinarith [norm_nonneg z]
  have hQ := (lim_poly _ _ ha).mp hb
  rw [← lim_core _ _ hv] at hQ
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  · exact Or.inr ((lim_claim_w w hw0).mp (by linarith))

/-- A square root `v` of `w + 3` with `Re v > 0` and the quartic negative gives a preimage `v - 2`. -/
theorem lim_finish (v w : ℂ) (hv : v ^ 2 = w + 3) (ha : 0 < v.re)
    (hQ : (v.re ^ 2 + v.im ^ 2) ^ 2 - 10 * v.re ^ 2 + 6 * v.im ^ 2 + 9 < 0) : w ∈ discImage polyFour := by
  have hb := (lim_poly v.re v.im ha).mpr hQ
  have hre : (v - 2).re = v.re - 2 := by simp
  have him : (v - 2).im = v.im := by simp
  have hn := lim_normSq (v - 2)
  rw [hre, him] at hn
  refine mem_discImage.mpr ⟨v - 2, ?_, ?_⟩
  · nlinarith [norm_nonneg (v - 2)]
  · rw [lim_eval]; linear_combination hv

/-- (⊇) of the region lemma. -/
theorem lim_sup (w : ℂ) (h : w = 0 ∨ ‖w‖ ^ 2 < 4 * ‖w‖ + 2 * w.re) : w ∈ discImage polyFour := by
  have hQw : ‖w‖ ^ 2 - 2 * w.re - 6 - 2 * ‖w + 3‖ < 0 := by
    by_cases hw0 : w = 0
    · subst hw0
      have h3 : ‖(0 : ℂ) + 3‖ = 3 := by
        rw [zero_add, show ((3 : ℂ)) = ((3 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by norm_num)]
      rw [h3]; norm_num
    · rcases h with h | h
      · exact absurd h hw0
      · have := (lim_claim_w w hw0).mpr h
        linarith
  have key : ∀ v : ℂ, v ^ 2 = w + 3 →
      (v.re ^ 2 + v.im ^ 2) ^ 2 - 10 * v.re ^ 2 + 6 * v.im ^ 2 + 9 < 0 := by
    intro v hv
    rw [← lim_core v w hv]
    exact hQw
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (w + 3) (n := 2) (by norm_num)
  have hv' : (-v) ^ 2 = w + 3 := by rw [neg_sq]; exact hv
  rcases lt_trichotomy v.re 0 with hneg | hzero | hpos
  · exact lim_finish (-v) w hv' (by rw [Complex.neg_re]; linarith) (key _ hv')
  · exfalso
    have hk := key v hv
    rw [hzero] at hk
    exact lim_poly_re_zero _ hk
  · exact lim_finish v w hv hpos (key v hv)

/-- (2) KEY: the image as an arg-free region. -/
theorem lim_region : discImage polyFour = {w : ℂ | w = 0 ∨ ‖w‖ ^ 2 < 4 * ‖w‖ + 2 * w.re} := by
  ext w
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hw
    obtain ⟨z, hz, rfl⟩ := mem_discImage.mp hw
    exact lim_sub z hz
  · exact lim_sup w

/-- The region in polar form. -/
theorem lim_arg_iff (w : ℂ) :
    (w = 0 ∨ ‖w‖ ^ 2 < 4 * ‖w‖ + 2 * w.re) ↔ ‖w‖ < 4 + 2 * Real.cos (Complex.arg w) := by
  by_cases hw : w = 0
  · subst hw
    have h0 : ‖(0 : ℂ)‖ < 4 + 2 * Real.cos (Complex.arg 0) := by
      rw [Complex.arg_zero, Real.cos_zero, norm_zero]; norm_num
    exact ⟨fun _ => h0, fun _ => Or.inl rfl⟩
  · have hs : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hx : w.re = ‖w‖ * Real.cos (Complex.arg w) := (Complex.norm_mul_cos_arg w).symm
    rw [hx]
    constructor
    · rintro (h | h)
      · exact absurd h hw
      · by_contra hc
        push Not at hc
        nlinarith [mul_le_mul_of_nonneg_left hc hs.le]
    · intro h
      right
      nlinarith [mul_lt_mul_of_pos_left h hs]

/-- (5) The disc `|w - 2| < 4` lies in the image. -/
theorem lim_ball : Metric.ball 2 4 ⊆ discImage polyFour := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  rw [lim_region]
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  · right
    have hs : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hre : (w - 2).re = w.re - 2 := by simp
    have him : (w - 2).im = w.im := by simp
    have h1 := lim_normSq (w - 2)
    rw [hre, him] at h1
    have h2 := lim_normSq w
    have h16 : ‖w - 2‖ ^ 2 < 16 := by nlinarith [norm_nonneg (w - 2)]
    have hA : ‖w‖ ^ 2 < 12 + 4 * w.re := by nlinarith
    have hx : -‖w‖ ≤ w.re := (abs_le.mp (Complex.abs_re_le_norm w)).1
    have hx2 : w.re ≤ ‖w‖ := Complex.re_le_norm w
    have h6 : ‖w‖ < 6 := by nlinarith
    by_cases h2le : 2 ≤ ‖w‖
    · nlinarith [mul_nonneg (sub_nonneg.mpr h2le) (sub_pos.mpr h6).le]
    · push Not at h2le
      nlinarith [mul_pos hs (sub_pos.mpr h2le)]

/-- (6) No disc of radius `> 4` lies in the image (the strip has width 8). -/
theorem lim_maxRadius (c : ℂ) (r : ℝ) (h : Metric.ball c r ⊆ discImage polyFour) : r ≤ 4 := by
  by_contra hr
  push Not at hr
  have h4 : ‖((4 : ℝ) : ℂ)‖ = 4 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hp : c + ((4 : ℝ) : ℂ) ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, h4]; exact hr
  have hm : c - ((4 : ℝ) : ℂ) ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, h4]; exact hr
  have hp' := (lim_strip _ (h hp)).2
  have hm' := (lim_strip _ (h hm)).1
  rw [Complex.add_re, Complex.ofReal_re] at hp'
  rw [Complex.sub_re, Complex.ofReal_re] at hm'
  linarith

/-- Row `fig2_limacon` (Figure 2): the limaçon `1 + 4z + z^2`. -/
theorem fig2_limacon_proved :
    (∀ ψ : ℝ, polyFour.eval (Complex.exp (ψ * Complex.I)) =
      ((4 + 2 * Real.cos ψ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) ∧
    discImage polyFour = {w : ℂ | ‖w‖ < 4 + 2 * Real.cos (Complex.arg w)} ∧
    (∀ w ∈ discImage polyFour, -2 < w.re ∧ w.re < 6) ∧
    coefMaxDeg polyFour = 4 ∧ Metric.ball 2 4 ⊆ discImage polyFour ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage polyFour → r ≤ 4) := by
  refine ⟨lim_circle, ?_, lim_strip, lim_coefMaxDeg, lim_ball, lim_maxRadius⟩
  rw [lim_region]
  ext w
  exact lim_arg_iff w

end Sheil

#print axioms Sheil.fig2_limacon_proved
