/- Sheil/Proofs/Sec3.lean — proofs of the rows exists_max_circle, lem_3_2, lem_3_2_closed of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Proofs.Lemma22

namespace Sheil.Proofs

open Polynomial ComplexConjugate
open scoped ComplexOrder

theorem exists_max_circle_proved (P : ℂ[X]) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ‖P.eval ζ‖ = maxMod P := by
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  obtain ⟨ζ, hζ, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_sSup_image_eq hne P.continuous.norm.continuousOn
  exact ⟨ζ, by simpa using hζ, hM.symm⟩

theorem lem_3_2_of_derivative_bound (n : ℕ) (hn : 1 ≤ n)
    (hbound : ∀ H : ℂ[X], H.natDegree ≤ n → (∀ z ∈ unitDisc, H.eval z ≠ 0) →
      ∀ z : ℂ, ‖z‖ = 1 → ‖z * H.derivative.eval z‖ ≤ ‖(n : ℂ) * H.eval z - z * H.derivative.eval z‖)
    (f : ℂ[X]) (hdeg : f.natDegree ≤ n) (z0 : ℂ) (hz0 : ‖z0‖ = 1)
    (hf' : f.derivative.eval z0 ≠ 0) :
    Metric.ball (f.eval z0 - z0 * f.derivative.eval z0 / n) (‖f.derivative.eval z0‖ / n) ⊆ discImage f := by
  intro w hw
  by_contra hwout
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hD : ∀ z ∈ unitDisc, (f - C w).eval z ≠ 0 := by
    intro z hz heq
    apply hwout
    refine ⟨z, hz, ?_⟩
    simpa using sub_eq_zero.mp (by simpa using heq : f.eval z - w = 0)
  have hd : (f - C w).natDegree ≤ n :=
    (natDegree_sub_le f (C w)).trans (max_le hdeg (by simpa using Nat.zero_le n))
  have hi := hbound (f - C w) hd hD z0 hz0
  simp only [derivative_sub, derivative_C, sub_zero, eval_sub, eval_C] at hi
  rw [norm_mul, hz0, one_mul] at hi
  have heq : (n : ℂ) * (f.eval z0 - w) - z0 * f.derivative.eval z0 =
      -((n : ℂ) * (w - (f.eval z0 - z0 * f.derivative.eval z0 / n))) := by
    field_simp
    <;> ring
  rw [heq, norm_neg, norm_mul, Complex.norm_natCast] at hi
  have hw' : ‖w - (f.eval z0 - z0 * f.derivative.eval z0 / n)‖ < ‖f.derivative.eval z0‖ / n := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hlt := (lt_div_iff₀ hnR).mp hw'
  nlinarith

theorem lem_3_2_closed_of_open (n : ℕ) (hn : 1 ≤ n) (f : ℂ[X]) (hdeg : f.natDegree ≤ n)
    (z0 : ℂ) (hz0 : ‖z0‖ = 1) (hf' : f.derivative.eval z0 ≠ 0)
    (hopen : Metric.ball (f.eval z0 - z0 * f.derivative.eval z0 / n) (‖f.derivative.eval z0‖ / n) ⊆ discImage f) :
    Metric.closedBall (f.eval z0 - z0 * f.derivative.eval z0 / n) (‖f.derivative.eval z0‖ / n) ⊆
      (fun z => f.eval z) '' Metric.closedBall (0 : ℂ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < ‖f.derivative.eval z0‖ / (n : ℝ) := div_pos (norm_pos_iff.mpr hf') hnR
  have hclosed : IsClosed ((fun z => f.eval z) '' Metric.closedBall (0 : ℂ) 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image f.continuous).isClosed
  have hsub : discImage f ⊆ (fun z => f.eval z) '' Metric.closedBall (0 : ℂ) 1 :=
    Set.image_mono Metric.ball_subset_closedBall
  have hc := hclosed.closure_subset_iff.mpr (hopen.trans hsub)
  simpa only [closure_ball _ (ne_of_gt hr)] using hc

theorem lem_3_2_proved (n : ℕ) (hn : 1 ≤ n) (f : ℂ[X]) (hdeg : f.natDegree ≤ n)
    (z0 : ℂ) (hz0 : ‖z0‖ = 1) (hf' : f.derivative.eval z0 ≠ 0) :
    Metric.ball (f.eval z0 - z0 * f.derivative.eval z0 / n) (‖f.derivative.eval z0‖ / n) ⊆ discImage f :=
  lem_3_2_of_derivative_bound n hn (lem_2_2_a_proved n) f hdeg z0 hz0 hf'

theorem lem_3_2_closed_proved (n : ℕ) (hn : 1 ≤ n) (f : ℂ[X]) (hdeg : f.natDegree ≤ n)
    (z0 : ℂ) (hz0 : ‖z0‖ = 1) (hf' : f.derivative.eval z0 ≠ 0) :
    Metric.closedBall (f.eval z0 - z0 * f.derivative.eval z0 / n) (‖f.derivative.eval z0‖ / n) ⊆
      (fun z => f.eval z) '' Metric.closedBall (0 : ℂ) 1 :=
  lem_3_2_closed_of_open n hn f hdeg z0 hz0 hf' (lem_3_2_proved n hn f hdeg z0 hz0 hf')

lemma maxMod_nonneg (P : ℂ[X]) : 0 ≤ maxMod P := by
  obtain ⟨ζ, _, hM⟩ := exists_max_circle_proved P
  rw [← hM]
  exact norm_nonneg _

lemma norm_eval_le_maxMod (P : ℂ[X]) (z : ℂ) (hz : ‖z‖ = 1) : ‖P.eval z‖ ≤ maxMod P := by
  apply le_csSup ((isCompact_sphere (0 : ℂ) 1).bddAbove_image P.continuous.norm.continuousOn)
  exact ⟨z, by simpa using hz, rfl⟩

lemma norm_eval_le_maxMod_closed (P : ℂ[X]) (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖P.eval z‖ ≤ maxMod P := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) 1) Metric.isBounded_ball
    P.differentiable.diffContOnCl ?_ ?_
  · intro u hu
    apply norm_eval_le_maxMod P u
    simpa only [frontier_ball (0 : ℂ) one_ne_zero, Metric.mem_sphere, dist_zero_right] using hu
  · rwa [closure_ball (0 : ℂ) one_ne_zero]

lemma discImage_subset_closedBall (P : ℂ[X]) : discImage P ⊆ Metric.closedBall (0 : ℂ) (maxMod P) := by
  rintro w ⟨z, hz, rfl⟩
  simpa using norm_eval_le_maxMod_closed P z (Metric.ball_subset_closedBall hz)

lemma discImage_subset_ball (P : ℂ[X]) (hnc : 0 < P.natDegree) :
    discImage P ⊆ Metric.ball (0 : ℂ) (maxMod P) := by
  have hopen : IsOpen (discImage P) :=
    (P.isOpenQuotientMap_eval (Nat.ne_of_gt hnc)).isOpenMap _ Metric.isOpen_ball
  have hi := interior_maximal (discImage_subset_closedBall P) hopen
  simpa only [interior_closedBall'] using hi

lemma maxMod_pos (P : ℂ[X]) (hnc : 0 < P.natDegree) : 0 < maxMod P := by
  have hmem : P.eval 0 ∈ discImage P := ⟨0, by simp [unitDisc], rfl⟩
  have hlt : ‖P.eval 0‖ < maxMod P := by simpa using discImage_subset_ball P hnc hmem
  exact (norm_nonneg _).trans_lt hlt

lemma upper_radius_of_zero_omitted (S : Set ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hzero : (0 : ℂ) ∉ S) (hS : S ⊆ Metric.closedBall (0 : ℂ) M)
    (c : ℂ) (r : ℝ) (hball : Metric.ball c r ⊆ S) : r ≤ M / 2 := by
  by_cases hr : 0 < r
  · have hmiss : r ≤ ‖c‖ := by
      by_contra h
      apply hzero
      apply hball
      simpa [Metric.mem_ball, dist_eq_norm] using lt_of_not_ge h
    have hc : 0 < ‖c‖ := hr.trans_le hmiss
    have hc0 : ‖c‖ ≠ 0 := ne_of_gt hc
    have hclosed : Metric.closedBall c r ⊆ Metric.closedBall (0 : ℂ) M := by
      rw [← closure_ball c (ne_of_gt hr)]
      exact Metric.isClosed_closedBall.closure_subset_iff.mpr (hball.trans hS)
    have hwdist : dist (((1 + r / ‖c‖ : ℝ)) • c) c = r := by
      rw [dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr.le hc.le), div_mul_cancel₀ _ hc0]
    have hwnorm : ‖((1 + r / ‖c‖ : ℝ)) • c‖ = ‖c‖ + r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
      <;> ring
    have hwmem := hclosed (Metric.mem_closedBall.mpr hwdist.le)
    have hwle : ‖((1 + r / ‖c‖ : ℝ)) • c‖ ≤ M := by simpa using hwmem
    rw [hwnorm] at hwle
    linarith
  · linarith

lemma circle_image_no_zero (P : ℂ[X]) (hz : ZerosOnCircle P) : (0 : ℂ) ∉ discImage P := by
  rintro ⟨z, hzD, hz0⟩
  have hz1 := hz z hz0
  have hzlt : ‖z‖ < 1 := by simpa [unitDisc] using hzD
  linarith

theorem thm_3_1_of_half_cover (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hM : ‖P.eval ζ‖ = maxMod P)
    (hhalf : Metric.ball (P.eval ζ / 2) (maxMod P / 2) ⊆ discImage P) :
    Metric.ball (P.eval ζ / 2) (maxMod P / 2) ⊆ discImage P ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage P → r ≤ maxMod P / 2) ∧
    ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔ 2 * coefMaxDeg P ≤ maxMod P) := by
  have hupper : ∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage P → r ≤ maxMod P / 2 :=
    upper_radius_of_zero_omitted (discImage P) (maxMod P) (maxMod_nonneg P)
      (circle_image_no_zero P hz) (discImage_subset_closedBall P)
  refine ⟨hhalf, hupper, ?_⟩
  constructor
  · rintro ⟨c, hc⟩
    linarith [hupper c (coefMaxDeg P) hc]
  · intro hA
    refine ⟨P.eval ζ / 2, (Metric.ball_subset_ball ?_).trans hhalf⟩
    linarith

end Sheil.Proofs
