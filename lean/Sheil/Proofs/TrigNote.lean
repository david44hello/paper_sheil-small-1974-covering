/- Sheil/Proofs/TrigNote.lean — proofs of the row coef_note_trig of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Proofs.Lemma21
import Sheil.Proofs.Lemma22

namespace Sheil.Proofs
open Polynomial ComplexConjugate

lemma trig_exp_real_norm (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma trig_phase_norm (m : ℕ) (θ : ℝ) :
    ‖Complex.exp (-(m : ℂ) * θ * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- Every `λ` with `P* = λP` has `|λ| = 1`: it is the `λ` of Lemma 2.1 (`P ≠ 0`). -/
lemma trig_lam_norm (P : ℂ[X]) (m : ℕ) (hm : 1 ≤ m) (hdeg : P.natDegree = 2 * m) (hz : ZerosOnCircle P)
    (lam : ℂ) (hlam : pstar (2 * m) P = C lam * P) : ‖lam‖ = 1 := by
  obtain ⟨_, lam0, hlam0, hst⟩ := lem_2_1_circle_proved P (by omega) hz
  rw [hdeg] at hst
  have hP : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hC : C lam = C lam0 := mul_right_cancel₀ hP (hlam.symm.trans hst)
  rw [C_inj.mp hC]
  exact hlam0

/-- `Q(θ) = e^{-imθ} P(e^{iθ})` (= `trigT 1`) has `conj Q = λ Q` on the real line when `P* = λP`. -/
lemma trig_conj_Q (P : ℂ[X]) (m : ℕ) (hdeg : P.natDegree ≤ 2 * m) (lam : ℂ)
    (hlam : pstar (2 * m) P = C lam * P) (θ : ℝ) :
    conj (trigT 1 m P θ) = lam * trigT 1 m P θ := by
  set z := Complex.exp ((θ : ℂ) * Complex.I) with hzdef
  have hn : ‖z‖ = 1 := trig_exp_real_norm θ
  have hi : (conj z)⁻¹ = z := conj_inv_eq_self_of_norm hn
  have he := pstar_eval_proved (2 * m) P hdeg z (Complex.exp_ne_zero _)
  rw [hlam, hi, eval_mul, eval_C] at he
  have hp : Complex.exp ((m : ℂ) * θ * Complex.I) =
      Complex.exp (-(m : ℂ) * θ * Complex.I) * z ^ (2 * m) := by
    rw [hzdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc : conj (-(m : ℂ) * θ * Complex.I) = (m : ℂ) * θ * Complex.I := by simp
  unfold trigT
  rw [map_mul, map_mul, map_one, ← Complex.exp_conj, hc, hp, ← hzdef]
  calc 1 * (Complex.exp (-(m : ℂ) * θ * Complex.I) * z ^ (2 * m)) * conj (P.eval z)
      = Complex.exp (-(m : ℂ) * θ * Complex.I) * (z ^ (2 * m) * conj (P.eval z)) := by ring
    _ = Complex.exp (-(m : ℂ) * θ * Complex.I) * (lam * P.eval z) := by rw [he]
    _ = lam * (1 * Complex.exp (-(m : ℂ) * θ * Complex.I) * P.eval z) := by ring

/-- `T = cQ` is real on the real line when `c^2 = λ` and `|c| = 1`. -/
lemma trig_real_of_sq (P : ℂ[X]) (m : ℕ) (hdeg : P.natDegree ≤ 2 * m) (lam c : ℂ)
    (hlam : pstar (2 * m) P = C lam * P) (hc : ‖c‖ = 1) (hsq : c ^ 2 = lam) (θ : ℝ) :
    (trigT c m P θ).im = 0 := by
  have hQ := trig_conj_Q P m hdeg lam hlam θ
  have hT : trigT c m P θ = c * trigT 1 m P θ := by
    unfold trigT
    ring
  have hcc : conj c * c = 1 := by
    rw [Complex.conj_mul', hc]
    simp
  apply Complex.conj_eq_iff_im.mp
  rw [hT, map_mul, hQ, ← hsq]
  linear_combination (c * trigT 1 m P θ) * hcc

lemma trig_expand (P : ℂ[X]) (m : ℕ) (hdeg : P.natDegree ≤ 2 * m)
    (c θ : ℂ) : trigT c m P θ =
    ∑ j ∈ Finset.range (2 * m + 1), c * P.coeff j * Complex.exp (((j : ℂ) - m) * θ * Complex.I) := by
  unfold trigT
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < 2 * m + 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.exp_nat_mul]
  have he : Complex.exp (((j : ℂ) - m) * θ * Complex.I) =
      Complex.exp (-(m : ℂ) * θ * Complex.I) * Complex.exp ((j : ℂ) * (θ * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- The top coefficient of `T` (frequency `m`) is `c a_n ≠ 0`: `T` has exact degree `m`. -/
lemma trig_top_ne (P : ℂ[X]) (m : ℕ) (hm : 1 ≤ m) (hdeg : P.natDegree = 2 * m) (c : ℂ) (hc : ‖c‖ = 1) :
    c * P.coeff (2 * m) ≠ 0 := by
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
  have hP : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hlead : P.coeff (2 * m) ≠ 0 := by
    rw [← hdeg]
    exact leadingCoeff_ne_zero.mpr hP
  exact mul_ne_zero hc0 hlead

/-- For complex `θ`: `T(θ) = 0` iff `e^{iθ}` is a zero of `P`. -/
lemma trig_zero_iff (P : ℂ[X]) (m : ℕ) (c : ℂ) (hc : ‖c‖ = 1) (θ : ℂ) :
    trigT c m P θ = 0 ↔ P.IsRoot (Complex.exp (θ * Complex.I)) := by
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
  have hne : c * Complex.exp (-(m : ℂ) * θ * Complex.I) ≠ 0 := mul_ne_zero hc0 (Complex.exp_ne_zero _)
  unfold trigT
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hne
  · intro h
    rw [h.eq_zero, mul_zero]

lemma trig_zeros (P : ℂ[X]) (m : ℕ) (hz : ZerosOnCircle P)
    (c : ℂ) (hc : ‖c‖ = 1) (θ : ℂ) (hT : trigT c m P θ = 0) : θ.im = 0 := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hP : P.eval (Complex.exp (θ * Complex.I)) = 0 :=
    (mul_eq_zero.mp hT).resolve_left (mul_ne_zero hc0 (Complex.exp_ne_zero _))
  have h := hz _ hP
  rw [Complex.norm_exp] at h
  have hzero := (Real.exp_eq_one_iff _).mp h
  simpa using hzero

/-- `t ↦ e^{it}` is injective on one period `[0, 2π)`. -/
lemma trig_exp_injOn (s t : ℝ) (hs : s ∈ Set.Ico 0 (2 * Real.pi)) (ht : t ∈ Set.Ico 0 (2 * Real.pi))
    (h : Complex.exp ((s : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * Complex.I)) : s = t := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hre : s = t + k * (2 * Real.pi) := by
    have him := congrArg Complex.im hk
    simp at him
    linarith
  have hpi := Real.pi_pos
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have h1 : (k : ℝ) < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h2 : (-1 : ℝ) < k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk0 : k = 0 := by
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    omega
  rw [hk0] at hre
  simpa using hre

/-- Every point of the unit circle is `e^{it}` for some `t` in one period `[0, 2π)`. -/
lemma trig_exp_surj (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ t ∈ Set.Ico 0 (2 * Real.pi), Complex.exp ((t : ℂ) * Complex.I) = z := by
  have he : Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z := by
    simpa [hz] using Complex.norm_mul_exp_arg_mul_I z
  have hpi := Real.pi_pos
  by_cases h0 : 0 ≤ Complex.arg z
  · exact ⟨Complex.arg z, ⟨h0, by linarith [Complex.arg_le_pi z]⟩, he⟩
  · refine ⟨Complex.arg z + 2 * Real.pi, ⟨by linarith [Complex.neg_pi_lt_arg z], by linarith⟩, ?_⟩
    push_cast
    rw [add_mul, Complex.exp_add, he, Complex.exp_two_pi_mul_I, mul_one]

/-- The zeros of `T` in one period `[0, 2π)` correspond one-to-one to the zeros of `P` (through `t ↦ e^{it}`). -/
lemma trig_period_bij (P : ℂ[X]) (m : ℕ) (hz : ZerosOnCircle P) (c : ℂ) (hc : ‖c‖ = 1) :
    Set.BijOn (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ trigT c m P t = 0} {z : ℂ | P.IsRoot z} := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (trig_zero_iff P m c hc t).mp ht.2
  · intro s hs t ht hst
    exact trig_exp_injOn s t hs.1 ht.1 hst
  · intro z hzr
    obtain ⟨t, ht, hte⟩ := trig_exp_surj z (hz z hzr)
    refine ⟨t, ⟨ht, ?_⟩, hte⟩
    rw [trig_zero_iff P m c hc, hte]
    exact hzr

lemma trig_sup (P : ℂ[X]) (m : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    sSup (Set.range (fun θ : ℝ => ‖trigT c m P θ‖)) = maxMod P := by
  have hn (θ : ℝ) : ‖trigT c m P θ‖ = ‖P.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
    simp only [trigT, norm_mul, hc, trig_phase_norm, one_mul]
  congr 1
  ext value
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨Complex.exp ((θ : ℂ) * Complex.I), by simp, (hn θ).symm⟩
  · rintro ⟨z, hz, rfl⟩
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have he : Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z := by
      simpa [hz1] using Complex.norm_mul_exp_arg_mul_I z
    exact ⟨Complex.arg z, by change ‖trigT c m P (Complex.arg z)‖ = ‖P.eval z‖; rw [hn, he]⟩

lemma trig_frequency_integral (j m : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (((j : ℂ) - m) * θ * Complex.I)) =
      if j = m then (2 * Real.pi : ℂ) else 0 := by
  by_cases hj : j = m
  · subst j
    simp
  · rw [ite_eq_right hj]
    have hf : ((j : ℂ) - m) * Complex.I ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hj)) Complex.I_ne_zero
    have he : Complex.exp ((((j : ℂ) - m) * Complex.I) * (2 * Real.pi)) = 1 := by
      have halg : (((j : ℂ) - m) * Complex.I) * (2 * Real.pi) =
          (j : ℂ) * (2 * Real.pi * Complex.I) - (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
      rw [halg, Complex.exp_sub, Complex.exp_nat_mul_two_pi_mul_I,
        Complex.exp_nat_mul_two_pi_mul_I, div_self one_ne_zero]
    have hi := integral_exp_mul_complex (a := (0 : ℝ)) (b := 2 * Real.pi) hf
    have halg (θ : ℝ) : ((j : ℂ) - m) * θ * Complex.I = (((j : ℂ) - m) * Complex.I) * θ := by ring
    simp_rw [halg]
    rw [hi]
    push_cast
    rw [he]
    simp

lemma trig_mean (P : ℂ[X]) (m : ℕ) (hdeg : P.natDegree ≤ 2 * m) (c : ℂ) :
    (1 / (2 * Real.pi) : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), trigT c m P θ) = c * P.coeff m := by
  simp_rw [trig_expand P m hdeg c]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, trig_frequency_integral]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_eq_single m]
    · simp
      field_simp
    · intro j _ hj
      simp [hj]
    · simp
      omega
  · intro j _
    exact (by fun_prop : Continuous (fun θ : ℝ =>
      c * P.coeff j * Complex.exp (((j : ℂ) - m) * θ * Complex.I))).intervalIntegrable _ _

/-- P025_body.tex:318-319: "the case `k = n/2` says that the constant term `t_0` of such a `T` satisfies
`|t_0| ≤ (1/2) max |T|`": for `|c| = 1`, `|a_m| ≤ M(P)/2` iff `|c a_m| ≤ (1/2) sup |T|`. -/
lemma trig_middle_iff (P : ℂ[X]) (m : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    ‖P.coeff m‖ ≤ maxMod P / 2 ↔
      ‖c * P.coeff m‖ ≤ sSup (Set.range (fun θ : ℝ => ‖trigT c m P θ‖)) / 2 := by
  rw [norm_mul, hc, one_mul, trig_sup P m c hc]

/-- Row `coef_note_trig` (N2), the note after Theorem 3.4, P025_body.tex:313-319. -/
theorem coef_note_trig_proved (P : ℂ[X]) (m : ℕ) (hm : 1 ≤ m) (hdeg : P.natDegree = 2 * m)
    (hz : ZerosOnCircle P) :
    (∃ lam : ℂ, ‖lam‖ = 1 ∧ pstar (2 * m) P = C lam * P) ∧
    ∀ lam : ℂ, pstar (2 * m) P = C lam * P →
      (∀ θ : ℝ, conj (trigT 1 m P θ) = lam * trigT 1 m P θ) ∧
      (∃ c : ℂ, c ^ 2 = lam) ∧
      ∀ c : ℂ, c ^ 2 = lam →
        ‖c‖ = 1 ∧ (∀ θ : ℝ, (trigT c m P θ).im = 0) ∧
        (∀ θ : ℂ, trigT c m P θ =
          ∑ j ∈ Finset.range (2 * m + 1), c * P.coeff j * Complex.exp (((j : ℂ) - m) * θ * Complex.I)) ∧
        c * P.coeff (2 * m) ≠ 0 ∧
        P.roots.card = 2 * m ∧
        (∀ θ : ℂ, trigT c m P θ = 0 ↔ P.IsRoot (Complex.exp (θ * Complex.I))) ∧
        (∀ θ : ℂ, trigT c m P θ = 0 → θ.im = 0) ∧
        Set.BijOn (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
          {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ trigT c m P t = 0} {z : ℂ | P.IsRoot z} ∧
        sSup (Set.range (fun θ : ℝ => ‖trigT c m P θ‖)) = maxMod P ∧
        (1 / (2 * Real.pi) : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), trigT c m P θ) = c * P.coeff m ∧
        (‖P.coeff m‖ ≤ maxMod P / 2 ↔
          ‖c * P.coeff m‖ ≤ sSup (Set.range (fun θ : ℝ => ‖trigT c m P θ‖)) / 2) := by
  obtain ⟨_, lam0, hlam0, hst⟩ := lem_2_1_circle_proved P (by omega) hz
  rw [hdeg] at hst
  refine ⟨⟨lam0, hlam0, hst⟩, fun lam hlam => ⟨trig_conj_Q P m hdeg.le lam hlam,
    IsAlgClosed.exists_pow_nat_eq lam (by norm_num), fun c hsq => ?_⟩⟩
  have hl1 : ‖lam‖ = 1 := trig_lam_norm P m hm hdeg hz lam hlam
  have hc : ‖c‖ = 1 := by
    have h := congrArg norm hsq
    rw [norm_pow, hl1] at h
    nlinarith [norm_nonneg c]
  exact ⟨hc, trig_real_of_sq P m hdeg.le lam c hlam hc hsq, trig_expand P m hdeg.le c,
    trig_top_ne P m hm hdeg c hc, IsAlgClosed.card_roots_eq_natDegree.trans hdeg, trig_zero_iff P m c hc,
    trig_zeros P m hz c hc, trig_period_bij P m hz c hc, trig_sup P m c hc, trig_mean P m hdeg.le c,
    trig_middle_iff P m c hc⟩

#print axioms coef_note_trig_proved

end Sheil.Proofs
