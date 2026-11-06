/- Sheil/Proofs/Lemma22.lean — proofs of the rows pstar_pstar, pstar_eval, pstar_norm_circle, lem_2_2_a_zero, eq_one_factor, lem_2_2_c and 1 more of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Proofs.Basic

namespace Sheil.Proofs

open Polynomial ComplexConjugate
open scoped ComplexOrder

theorem pstar_pstar_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) :
    pstar n (pstar n H) = H := by
  ext k
  rw [coeff_pstar]
  by_cases hk : k ≤ n
  · rw [ite_eq_left hk, coeff_pstar, ite_eq_left (Nat.sub_le n k)]
    simp [Nat.sub_sub_self hk]
  · rw [ite_eq_right hk, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (Nat.lt_of_not_le hk))]

theorem pstar_eval_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (z : ℂ) (hz : z ≠ 0) :
    (pstar n H).eval z = z ^ n * conj (H.eval (conj z)⁻¹) := by
  letI : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have href := eval₂_reflect_mul_pow (starRingEnd ℂ) z⁻¹ n H hdeg
  simp only [invOf_eq_inv, inv_inv] at href
  have hev : H.eval₂ (starRingEnd ℂ) z⁻¹ = conj (H.eval (conj z)⁻¹) := by
    simpa using (eval₂_at_apply (p := H) (starRingEnd ℂ) ((conj z)⁻¹))
  rw [pstar_eq_reflect_map n H hdeg, eval_map]
  calc
    (H.reflect n).eval₂ (starRingEnd ℂ) z =
        ((H.reflect n).eval₂ (starRingEnd ℂ) z * (z⁻¹) ^ n) * z ^ n := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]
    _ = z ^ n * conj (H.eval (conj z)⁻¹) := by rw [href, hev, mul_comm]

theorem pstar_norm_circle_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(pstar n H).eval z‖ = ‖H.eval z‖ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hzi : (conj z)⁻¹ = z := by
    apply inv_eq_of_mul_eq_one_right
    simpa [hz] using Complex.conj_mul' z
  rw [pstar_eval_proved n H hdeg z hz0, norm_mul, norm_pow, hz, one_pow, one_mul, hzi]
  exact RCLike.norm_conj _

theorem lem_2_2_a_zero_proved (n : ℕ) (H : ℂ[X]) (z : ℂ) (hz0 : H.eval z = 0) :
    ‖z * H.derivative.eval z‖ = ‖(n : ℂ) * H.eval z - z * H.derivative.eval z‖ := by
  simp [hz0]

theorem eq_one_factor_proved (beta z eta : ℂ) :
    (1 - conj beta * z) * (1 - beta * conj eta) - (z - beta) * (conj eta - conj beta) =
      ((1 - ‖beta‖ ^ 2 : ℝ) : ℂ) * (1 - z * conj eta) := by
  push_cast
  rw [← Complex.mul_conj']
  ring

theorem lem_2_2_c_proved (n : ℕ) (H : ℂ[X]) (j : Fin n) :
    schurCohn n H j j = ∑ r ∈ Finset.range ((j : ℕ) + 1), ((‖H.coeff r‖ ^ 2 - ‖H.coeff (n - r)‖ ^ 2 : ℝ) : ℂ) ∧
    schurCohn n H ⟨0, Nat.zero_lt_of_lt j.isLt⟩ j =
      H.coeff 0 * conj (H.coeff j) - conj (H.coeff n) * H.coeff (n - j) := by
  constructor
  · unfold schurCohn
    simp only [min_self]
    rw [← Finset.sum_range_reflect
      (fun r => ((‖H.coeff r‖ ^ 2 - ‖H.coeff (n - r)‖ ^ 2 : ℝ) : ℂ)) ((j : ℕ) + 1)]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro r hr
    have hrj : r ≤ (j : ℕ) := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hidx : n - (j : ℕ) + r = n - ((j : ℕ) - r) := by omega
    rw [hidx, Complex.mul_conj', Complex.conj_mul']
    push_cast
    rfl
  · simp [schurCohn]

lemma root_term_re_le_half (z root : ℂ) (hz : ‖z‖ = 1) (hr : 1 ≤ ‖root‖)
    (hne : z - root ≠ 0) : (z / (z - root)).re ≤ (1 : ℝ) / 2 := by
  have hzsq : z.re * z.re + z.im * z.im = 1 := by
    have hs : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
    simpa [Complex.sq_norm, Complex.normSq_apply] using hs
  have hrsq : 1 ≤ root.re * root.re + root.im * root.im := by
    have hs : 1 ≤ ‖root‖ ^ 2 := by nlinarith [norm_nonneg root]
    simpa [Complex.sq_norm, Complex.normSq_apply] using hs
  have hpos : 0 < RCLike.normSq (z - root) := RCLike.normSq_pos.mpr hne
  change RCLike.re (z / (z - root)) ≤ _
  rw [RCLike.div_re, ← add_div, div_le_iff₀ hpos]
  simp only [RCLike.normSq_apply, map_sub] at *
  change z.re * (z.re - root.re) + z.im * (z.im - root.im) ≤
    1 / 2 * ((z.re - root.re) * (z.re - root.re) + (z.im - root.im) * (z.im - root.im))
  nlinarith

lemma sum_root_terms_re_le (roots : Multiset ℂ) (z : ℂ) (hz : ‖z‖ = 1)
    (hr : ∀ root ∈ roots, 1 ≤ ‖root‖) (hne : ∀ root ∈ roots, z - root ≠ 0) :
    ((roots.map (fun root => z / (z - root))).sum).re ≤ (roots.card : ℝ) / 2 := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons root roots ih =>
    have hroot := root_term_re_le_half z root hz (hr root (by simp)) (hne root (by simp))
    have hrest := ih (fun r h => hr r (by simp [h])) (fun r h => hne r (by simp [h]))
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one]
    linarith

lemma norm_le_nat_mul_sub_of_re_div_le (n : ℕ) (u v : ℂ) (hv : v ≠ 0)
    (hre : (u / v).re ≤ (n : ℝ) / 2) : ‖u‖ ≤ ‖(n : ℂ) * v - u‖ := by
  have hpos : 0 < RCLike.normSq v := RCLike.normSq_pos.mpr hv
  change RCLike.re (u / v) ≤ _ at hre
  rw [RCLike.div_re, ← add_div, div_le_iff₀ hpos] at hre
  simp only [RCLike.normSq_apply] at hre
  change u.re * v.re + u.im * v.im ≤ (n : ℝ) / 2 * (v.re * v.re + v.im * v.im) at hre
  have hmul := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    (show 0 ≤ (n : ℝ) * (v.re * v.re + v.im * v.im) -
      2 * (u.re * v.re + u.im * v.im) by nlinarith [hre])
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  nlinarith [hmul]

theorem lem_2_2_a_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n)
    (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z * H.derivative.eval z‖ ≤ ‖(n : ℂ) * H.eval z - z * H.derivative.eval z‖ := by
  by_cases hzero : H.eval z = 0
  · exact (lem_2_2_a_zero_proved n H z hzero).le
  have hr : ∀ root ∈ H.roots, 1 ≤ ‖root‖ := by
    intro root hroot
    by_contra hsmall
    have hmem : root ∈ unitDisc := by
      simpa [unitDisc, Metric.mem_ball, dist_zero_right] using (lt_of_not_ge hsmall)
    exact hD root hmem (isRoot_of_mem_roots hroot)
  have hne : ∀ root ∈ H.roots, z - root ≠ 0 := by
    intro root hroot heq
    have hzroot : z = root := sub_eq_zero.mp heq
    exact hzero (hzroot ▸ isRoot_of_mem_roots hroot)
  have hlog := (IsAlgClosed.splits H).eval_derivative_div_eval_of_ne_zero hzero
  have hratio : z * H.derivative.eval z / H.eval z =
      (H.roots.map (fun root => z / (z - root))).sum := by
    rw [mul_div_assoc, hlog, ← Multiset.sum_map_mul_left]
    simp only [mul_one_div]
  apply norm_le_nat_mul_sub_of_re_div_le n _ _ hzero
  rw [hratio]
  calc
    ((H.roots.map (fun root => z / (z - root))).sum).re ≤ (H.roots.card : ℝ) / 2 :=
      sum_root_terms_re_le H.roots z hz hr hne
    _ ≤ (n : ℝ) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast (card_roots' H).trans hdeg

end Sheil.Proofs
