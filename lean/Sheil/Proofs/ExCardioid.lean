/- Sheil/Proofs/ExCardioid.lean — proofs of the row fig2_cardioid of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Mathlib
import Sheil.Defs.Basic
import Sheil.Defs.Examples

namespace Sheil

open Polynomial ComplexConjugate
open scoped ComplexOrder

/-! ### Small algebraic facts about squares in `ℂ` -/

theorem card_norm_sq_eq (u : ℂ) : ‖u ^ 2‖ = u.re ^ 2 + u.im ^ 2 := by
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring

theorem card_sq_re (u : ℂ) : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by
  rw [sq, Complex.mul_re]; ring

theorem card_norm_sq_parts (u : ℂ) : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem card_eval (z : ℂ) : polyCardioid.eval z = (1 + z) ^ 2 := by
  simp [polyCardioid]

theorem card_mem_iff {w : ℂ} : w ∈ discImage polyCardioid ↔ ∃ z : ℂ, ‖z‖ < 1 ∧ (1 + z) ^ 2 = w := by
  simp [discImage, unitDisc, Metric.mem_ball, dist_zero_right, card_eval]

/-! ### (1) The circle formula -/

theorem card_circle (ψ : ℝ) : polyCardioid.eval (Complex.exp (ψ * Complex.I)) =
    ((2 + 2 * Real.cos ψ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I) := by
  have h1 : Complex.exp (-(ψ : ℂ) * Complex.I) * Complex.exp (ψ * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  have h2 : (2 : ℂ) * Complex.cos (ψ : ℂ) =
      Complex.exp (ψ * Complex.I) + Complex.exp (-(ψ : ℂ) * Complex.I) := Complex.two_cos (ψ : ℂ)
  rw [card_eval, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  linear_combination (-1 : ℂ) * h1 - Complex.exp (ψ * Complex.I) * h2

/-! ### (2) The region, first without `arg` -/

/-- One direction of the region: a point of the disc maps into `{w ≠ 0, ‖w‖² < 2‖w‖ + 2 Re w}`. -/
theorem card_region_sub (z : ℂ) (hz : ‖z‖ < 1) :
    (1 + z) ^ 2 ≠ 0 ∧ ‖(1 + z) ^ 2‖ ^ 2 < 2 * ‖(1 + z) ^ 2‖ + 2 * ((1 + z) ^ 2).re := by
  have hz2 : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h0 := card_norm_sq_parts z
    nlinarith [norm_nonneg z]
  have hre : (1 + z).re = 1 + z.re := by simp
  have him : (1 + z).im = z.im := by simp
  rw [card_norm_sq_eq, card_sq_re, hre, him]
  set a := 1 + z.re with ha
  set b := z.im with hb
  have hlt : a ^ 2 + b ^ 2 < 2 * a := by nlinarith
  have hapos : 0 < a := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hrho : 0 < a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg b]
  refine ⟨?_, ?_⟩
  · intro h0
    have h1 : ‖(1 + z) ^ 2‖ = 0 := by rw [h0, norm_zero]
    rw [card_norm_sq_eq, hre, him] at h1
    linarith
  · have hprod : 0 < (2 * a - (a ^ 2 + b ^ 2)) * (2 * a + (a ^ 2 + b ^ 2)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hprod]

/-- The other direction: a square root with nonnegative real part gives a disc point. -/
theorem card_region_sup (v w : ℂ) (hv : v ^ 2 = w) (hre : 0 ≤ v.re)
    (h : ‖w‖ ^ 2 < 2 * ‖w‖ + 2 * w.re) : ‖v - 1‖ < 1 := by
  rw [← hv, card_norm_sq_eq, card_sq_re] at h
  set a := v.re with ha
  set b := v.im with hb
  have hsq : (a ^ 2 + b ^ 2) ^ 2 < (2 * a) ^ 2 := by nlinarith
  have hlt : a ^ 2 + b ^ 2 < 2 * a := by
    by_contra hcon
    push Not at hcon
    have h2a : 0 ≤ 2 * a := by linarith
    nlinarith [mul_le_mul hcon hcon h2a (by positivity)]
  have hn : ‖v - 1‖ ^ 2 < 1 := by
    rw [card_norm_sq_parts]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg (v - 1)]

theorem card_region :
    discImage polyCardioid = {w : ℂ | w ≠ 0 ∧ ‖w‖ ^ 2 < 2 * ‖w‖ + 2 * w.re} := by
  ext w
  rw [card_mem_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact card_region_sub z hz
  · rintro ⟨_, h⟩
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq w (by norm_num : 0 < 2)
    by_cases hre : 0 ≤ u.re
    · exact ⟨u - 1, card_region_sup u w hu hre h, by rw [← hu]; ring⟩
    · have hu' : (-u) ^ 2 = w := by rw [← hu]; ring
      have hre' : 0 ≤ (-u).re := by simp only [Complex.neg_re]; linarith
      exact ⟨-u - 1, card_region_sup (-u) w hu' hre' h, by rw [← hu']; ring⟩

/-- The row's form of the region, with `arg`. -/
theorem card_region_arg :
    discImage polyCardioid = {w : ℂ | w ≠ 0 ∧ ‖w‖ < 2 + 2 * Real.cos (Complex.arg w)} := by
  rw [card_region]
  ext w
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨hw, ?_⟩
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hc := Complex.norm_mul_cos_arg w
    by_contra hcon
    push Not at hcon
    nlinarith [mul_le_mul_of_nonneg_left hcon hpos.le]
  · rintro ⟨hw, h⟩
    refine ⟨hw, ?_⟩
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hc := Complex.norm_mul_cos_arg w
    nlinarith [mul_lt_mul_of_pos_left h hpos]

/-! ### (3) Zeros, (4) `M = 4`, (5) `A = 2` -/

theorem card_zeros : ZerosOnCircle polyCardioid := by
  intro z hz
  have h : (1 + z) ^ 2 = 0 := by rw [← card_eval]; exact hz
  have h1 : 1 + z = 0 := pow_eq_zero_iff (by norm_num) |>.mp h
  have h2 : z = -1 := by linear_combination h1
  rw [h2]; simp

theorem card_maxMod : maxMod polyCardioid = 4 := by
  unfold maxMod
  apply IsGreatest.csSup_eq
  refine ⟨⟨1, by simp, ?_⟩, ?_⟩
  · simp only [card_eval]; norm_num
  · rintro x ⟨z, hz, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hz
    simp only [card_eval, norm_pow]
    have h1 : ‖1 + z‖ ≤ 2 := by
      calc ‖1 + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
        _ = 2 := by rw [hz]; norm_num
    nlinarith [norm_nonneg (1 + z)]

theorem card_eq_quad : polyCardioid = C 1 * X ^ 2 + C 2 * X + C 1 := by
  have h2 : (C (2 : ℂ) : ℂ[X]) = 2 := by simp [map_ofNat]
  rw [h2, polyCardioid, map_one]
  ring

theorem card_natDegree : polyCardioid.natDegree = 2 := by
  rw [card_eq_quad]; exact natDegree_quadratic one_ne_zero

theorem card_coeff (k : ℕ) : polyCardioid.coeff k =
    if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 1 else 0 := by
  rw [card_eq_quad]
  rcases k with _ | _ | _ | k <;> simp [coeff_X, coeff_C, coeff_X_pow, coeff_one]

theorem card_coefMaxDeg : coefMaxDeg polyCardioid = 2 := by
  unfold coefMaxDeg coefMax
  rw [card_natDegree]
  apply le_antisymm
  · apply Finset.sup'_le
    intro k hk
    have hk3 : k < 3 := Finset.mem_range.mp hk
    interval_cases k <;> simp [card_coeff]
  · have h1 : ‖polyCardioid.coeff 1‖ = 2 := by simp [card_coeff]
    rw [← h1]
    exact Finset.le_sup' (fun k => ‖polyCardioid.coeff k‖) (Finset.mem_range.mpr (by norm_num))

/-! ### (6) `D(2,2)` lies inside, (7) it is the only disc of radius `2` and no disc is larger -/

theorem card_ball_sub : Metric.ball 2 2 ⊆ discImage polyCardioid := by
  intro w hw
  rw [Metric.mem_ball, Complex.dist_eq] at hw
  rw [card_region]
  have hsq : ‖w - 2‖ ^ 2 < 4 := by nlinarith [norm_nonneg (w - 2)]
  rw [card_norm_sq_parts] at hsq
  simp only [Complex.sub_re, Complex.sub_im] at hsq
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have h2im : (2 : ℂ).im = 0 := by norm_num
  rw [h2re, h2im] at hsq
  have hparts := card_norm_sq_parts w
  have hle := Complex.re_le_norm w
  have hrepos : 0 < w.re := by nlinarith [sq_nonneg w.im, sq_nonneg w.re]
  refine ⟨?_, ?_⟩
  · intro h0; rw [h0] at hrepos; simp at hrepos
  · nlinarith [norm_nonneg w]

/-- Every image point has norm `< 4`. -/
theorem card_norm_lt_four {w : ℂ} (hw : w ∈ discImage polyCardioid) : ‖w‖ < 4 := by
  rw [card_region] at hw
  obtain ⟨hw0, h⟩ := hw
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hle := Complex.re_le_norm w
  nlinarith

/-- Points on the ray from `0` through `c`, beyond `c`. -/
theorem card_ray (c : ℂ) (hc : c ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖c * ((1 + t / ‖c‖ : ℝ) : ℂ)‖ = ‖c‖ + t ∧ dist (c * ((1 + t / ‖c‖ : ℝ) : ℂ)) c = t ∧
      (c * ((1 + t / ‖c‖ : ℝ) : ℂ)).re = c.re * (1 + t / ‖c‖) := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hs : 0 ≤ t / ‖c‖ := div_nonneg ht hpos.le
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    field_simp
  · rw [Complex.dist_eq]
    have he : c * ((1 + t / ‖c‖ : ℝ) : ℂ) - c = c * ((t / ‖c‖ : ℝ) : ℂ) := by push_cast; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    field_simp
  · simp [Complex.mul_re]

theorem card_ball_max (c : ℂ) (r : ℝ) (hsub : Metric.ball c r ⊆ discImage polyCardioid) :
    r ≤ 2 ∧ (r = 2 → c = 2) := by
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨by linarith, fun h => by linarith⟩
  have hcin : c ∈ discImage polyCardioid := hsub (Metric.mem_ball_self hr)
  have hc0 : c ≠ 0 := by
    have := hcin; rw [card_region] at this; exact this.1
  have hc4 : ‖c‖ < 4 := card_norm_lt_four hcin
  -- `0` is not in the image, so it is not in the ball: `r ≤ ‖c‖`.
  have hrc : r ≤ ‖c‖ := by
    by_contra hcon
    push Not at hcon
    have h0 : (0 : ℂ) ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_comm, dist_zero_right]; exact hcon
    have := hsub h0
    rw [card_region] at this
    exact this.1 rfl
  -- The ray points stay in the ball, hence have norm `< 4`: `‖c‖ + r ≤ 4`.
  have hray : ∀ t : ℝ, 0 ≤ t → t < r → ‖c‖ + t < 4 := by
    intro t ht htr
    obtain ⟨hn, hd, _⟩ := card_ray c hc0 t ht
    have hin : c * ((1 + t / ‖c‖ : ℝ) : ℂ) ∈ Metric.ball c r := by
      rw [Metric.mem_ball, hd]; exact htr
    have := card_norm_lt_four (hsub hin)
    rw [hn] at this; exact this
  have hsum : ‖c‖ + r ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have := hray (4 - ‖c‖) (by linarith) (by linarith)
    linarith
  refine ⟨by linarith, ?_⟩
  intro hr2
  have hc2 : ‖c‖ = 2 := by linarith
  -- On the ray, the region inequality gives `t < Re c` for every `0 ≤ t < 2`.
  have hreal : ∀ t : ℝ, 0 ≤ t → t < 2 → t < c.re := by
    intro t ht ht2
    obtain ⟨hn, hd, hre⟩ := card_ray c hc0 t ht
    have hin : c * ((1 + t / ‖c‖ : ℝ) : ℂ) ∈ Metric.ball c r := by
      rw [Metric.mem_ball, hd, hr2]; exact ht2
    have hmem := hsub hin
    rw [card_region] at hmem
    obtain ⟨_, hineq⟩ := hmem
    rw [hn, hre, hc2] at hineq
    have hfac : (2 + t) * (t - c.re) < 0 := by nlinarith
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + t) (by linarith : (0 : ℝ) ≤ t - c.re)]
  have hre2 : 2 ≤ c.re := by
    by_contra hcon
    push Not at hcon
    have := hreal (max c.re 0) (le_max_right _ _) (max_lt hcon (by norm_num))
    linarith [le_max_left c.re 0]
  have hle := Complex.re_le_norm c
  have hparts := card_norm_sq_parts c
  have hre_eq : c.re = 2 := by linarith
  have him : c.im = 0 := by
    rw [hc2, hre_eq] at hparts
    nlinarith [sq_nonneg c.im]
  apply Complex.ext
  · rw [hre_eq]; norm_num
  · rw [him]; norm_num

/-! ### The row -/

theorem fig2_cardioid_proved :
    (∀ ψ : ℝ, polyCardioid.eval (Complex.exp (ψ * Complex.I)) =
      ((2 + 2 * Real.cos ψ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) ∧
    discImage polyCardioid = {w : ℂ | w ≠ 0 ∧ ‖w‖ < 2 + 2 * Real.cos (Complex.arg w)} ∧
    ZerosOnCircle polyCardioid ∧ maxMod polyCardioid = 4 ∧ coefMaxDeg polyCardioid = 2 ∧
    Metric.ball 2 2 ⊆ discImage polyCardioid ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage polyCardioid → r ≤ 2 ∧ (r = 2 → c = 2)) :=
  ⟨card_circle, card_region_arg, card_zeros, card_maxMod, card_coefMaxDeg, card_ball_sub, card_ball_max⟩

end Sheil

#print axioms Sheil.fig2_cardioid_proved
