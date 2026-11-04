/- Sheil/Proofs/MaxPoint.lean — proofs of the rows prop_3_3, thm_3_1 of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Proofs.Sec3
import Sheil.Proofs.Lemma21

namespace Sheil.Proofs

open Polynomial ComplexConjugate

lemma coeff_euler (F : ℂ[X]) (k : ℕ) :
    (X * F.derivative).coeff k = (k : ℂ) * F.coeff k := by
  cases k with
  | zero => simp
  | succ k => simp [coeff_X_mul, coeff_derivative, mul_comm]

lemma euler_natDegree_le (n : ℕ) (F : ℂ[X]) (hdeg : F.natDegree ≤ n) :
    (X * F.derivative).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_euler, coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hk), mul_zero]

lemma pstar_euler (n : ℕ) (F : ℂ[X]) :
    pstar n (X * F.derivative) = C (n : ℂ) * pstar n F - X * (pstar n F).derivative := by
  ext k
  rw [coeff_pstar, coeff_sub, coeff_C_mul, coeff_euler]
  by_cases hk : k ≤ n
  · rw [ite_eq_left hk, coeff_euler, coeff_pstar, ite_eq_left hk]
    simp only [map_mul, map_natCast]
    rw [Nat.cast_sub hk]
    ring
  · rw [ite_eq_right hk, coeff_pstar, ite_eq_right hk]
    rw [coeff_euler, coeff_pstar, ite_eq_right hk]
    simp

lemma maximum_angular_stationary (F : ℂ[X]) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hM : ‖F.eval ζ‖ = maxMod F) :
    ((ζ * F.derivative.eval ζ) * conj (F.eval ζ)).im = 0 := by
  let curve : ℂ → ℂ := fun t => F.eval (ζ * Complex.exp (t * Complex.I))
  have hexp : HasDerivAt (fun t : ℂ => Complex.exp (t * Complex.I)) Complex.I 0 := by
    convert! (Complex.hasDerivAt_exp ((0 : ℂ) * Complex.I)).comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).mul_const Complex.I) using 1 <;> simp [Function.comp_def]
  have hcurve : HasDerivAt curve (F.derivative.eval ζ * (ζ * Complex.I)) 0 := by
    convert! (F.hasDerivAt (ζ * Complex.exp ((0 : ℂ) * Complex.I))).comp (0 : ℂ) (hexp.const_mul ζ) using 1 <;>
      simp [curve, Function.comp_def]
  have hlocal : IsLocalMax (fun t : ℝ => ‖curve t‖ ^ 2) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hcircle : ‖ζ * Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
      simp [norm_mul, hζ, Complex.norm_exp, Complex.mul_re]
    have hb := norm_eval_le_maxMod F (ζ * Complex.exp ((t : ℂ) * Complex.I)) hcircle
    rw [← hM] at hb
    simpa [curve] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb
  have hcrit := hlocal.hasDerivAt_eq_zero hcurve.comp_ofReal.norm_sq
  simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply] at hcrit
  have heq : (F.derivative.eval ζ * (ζ * Complex.I)) * conj (F.eval ζ) =
      ((ζ * F.derivative.eval ζ) * conj (F.eval ζ)) * Complex.I := by ring
  have hcrit' : 2 * ((F.derivative.eval ζ * (ζ * Complex.I)) * conj (F.eval ζ)).re = 0 := by
    simpa [curve] using hcrit
  rw [heq, Complex.mul_I_re] at hcrit'
  linarith

lemma maximum_point_identity (n : ℕ) (F : ℂ[X]) (hdeg : F.natDegree ≤ n)
    (hnc : 0 < F.natDegree) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hF : pstar n F = C lam * F) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hM : ‖F.eval ζ‖ = maxMod F) : ζ * F.derivative.eval ζ = ((n : ℂ) / 2) * F.eval ζ := by
  have hz0 : ζ ≠ 0 := by intro h; simp [h] at hζ
  have hlam0 : lam ≠ 0 := by intro h; simp [h] at hlam
  have hzi : (conj ζ)⁻¹ = ζ := by
    apply inv_eq_of_mul_eq_one_right
    simpa [hζ] using Complex.conj_mul' ζ
  have hval := pstar_eval_proved n F hdeg ζ hz0
  rw [hF, eval_mul, eval_C, hzi] at hval
  have hraw := congrArg (fun p : ℂ[X] => p.eval ζ) (pstar_euler n F)
  rw [pstar_eval_proved n _ (euler_natDegree_le n F hdeg) ζ hz0, hzi] at hraw
  simp [hF] at hraw
  have him := maximum_angular_stationary F ζ hζ hM
  have hprod : F.eval ζ * conj (ζ * F.derivative.eval ζ) =
      ((n : ℂ) * F.eval ζ - ζ * F.derivative.eval ζ) * conj (F.eval ζ) := by
    rw [map_mul]
    apply mul_left_cancel₀ hlam0
    linear_combination (conj ζ * conj (F.derivative.eval ζ)) * hval + (conj (F.eval ζ)) * hraw
  have hreal : F.eval ζ * conj (ζ * F.derivative.eval ζ) =
      (ζ * F.derivative.eval ζ) * conj (F.eval ζ) := by
    calc
      _ = conj ((ζ * F.derivative.eval ζ) * conj (F.eval ζ)) := by simp; ring
      _ = _ := Complex.conj_eq_iff_im.mpr him
  rw [hreal] at hprod
  have hF0 : F.eval ζ ≠ 0 := by
    have hpos := maxMod_pos F hnc
    rw [← hM] at hpos
    exact norm_pos_iff.mp hpos
  have hcF0 : conj (F.eval ζ) ≠ 0 := by simpa using hF0
  apply mul_right_cancel₀ hcF0
  linear_combination (1 / 2 : ℂ) * hprod

theorem prop_3_3_proved (n : ℕ) (F : ℂ[X]) (hdeg : F.natDegree ≤ n) (hnc : 0 < F.natDegree)
    (lam : ℂ) (hlam : ‖lam‖ = 1) (hF : pstar n F = C lam * F) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hM : ‖F.eval ζ‖ = maxMod F) :
    ζ * F.derivative.eval ζ = ((n : ℂ) / 2) * F.eval ζ ∧ F.derivative.eval ζ ≠ 0 ∧
    Metric.ball (F.eval ζ / 2) (maxMod F / 2) ⊆ discImage F := by
  have hn : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hid := maximum_point_identity n F hdeg hnc lam hlam hF ζ hζ hM
  have hF0 : F.eval ζ ≠ 0 := by
    have hpos := maxMod_pos F hnc
    rw [← hM] at hpos
    exact norm_pos_iff.mp hpos
  have hderiv : F.derivative.eval ζ ≠ 0 := by
    have hu : ζ * F.derivative.eval ζ ≠ 0 := by
      rw [hid]
      exact mul_ne_zero (div_ne_zero hnC (by norm_num)) hF0
    exact (mul_ne_zero_iff.mp hu).2
  refine ⟨hid, hderiv, ?_⟩
  have hcover := lem_3_2_proved n hn F hdeg ζ hζ hderiv
  have hcenter : F.eval ζ - ζ * F.derivative.eval ζ / n = F.eval ζ / 2 := by
    rw [hid]
    field_simp
    <;> ring
  have hnorm : ‖F.derivative.eval ζ‖ = (n : ℝ) / 2 * maxMod F := by
    have hh := congrArg norm hid
    simpa [norm_mul, norm_div, hζ, hM, Complex.norm_natCast] using hh
  have hradius : ‖F.derivative.eval ζ‖ / (n : ℝ) = maxMod F / 2 := by
    apply (div_eq_iff (ne_of_gt hnR)).mpr
    linarith [hnorm]
  simpa only [hcenter, hradius] using hcover

theorem thm_3_1_of_selfInversive (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hM : ‖P.eval ζ‖ = maxMod P) (hself : SelfInversive P) :
    Metric.ball (P.eval ζ / 2) (maxMod P / 2) ⊆ discImage P ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage P → r ≤ maxMod P / 2) ∧
    ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔ 2 * coefMaxDeg P ≤ maxMod P) := by
  obtain ⟨_, lam, hlam, hstar⟩ := hself
  exact thm_3_1_of_half_cover P hdeg hz ζ hζ hM
    (prop_3_3_proved P.natDegree P le_rfl hdeg lam hlam hstar ζ hζ hM).2.2

theorem thm_3_1_proved (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hM : ‖P.eval ζ‖ = maxMod P) :
    Metric.ball (P.eval ζ / 2) (maxMod P / 2) ⊆ discImage P ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage P → r ≤ maxMod P / 2) ∧
    ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔ 2 * coefMaxDeg P ≤ maxMod P) :=
  thm_3_1_of_selfInversive P hdeg hz ζ hζ hM (Sheil.lem_2_1_circle_proved P hdeg hz)

end Sheil.Proofs
