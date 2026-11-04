/- Sheil/Proofs/Rows.lean — proofs of the rows abs_M_two_A_iff, fig1_inclusions, abs_self_inversive, abs_zeros_conj_inv, abs_zeros_inv, abs_plus_minus and 9 more of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Proofs.Sec3
import Sheil.Proofs.Sec4
import Sheil.Proofs.Lemma21

namespace Sheil

open Polynomial ComplexConjugate
open scoped ComplexOrder

/-- The row `thm_3_1` (Theorem 3.1, P025_body.tex:258-262) as a hypothesis type. -/
def Hyp31 : Prop :=
  ∀ (P : ℂ[X]), 1 ≤ P.natDegree → ZerosOnCircle P → ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖P.eval ζ‖ = maxMod P →
    Metric.ball (P.eval ζ / 2) (maxMod P / 2) ⊆ discImage P ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage P → r ≤ maxMod P / 2) ∧
    ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔ 2 * coefMaxDeg P ≤ maxMod P)

/-- The row `thm_4_1` (Theorem 4.1, P025_body.tex:334-339) as a hypothesis type. -/
def HypThm41 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (P : ℂ[X]), P.natDegree ≤ n → 0 < P.natDegree → Mirror n P →
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P

/-- The statement of Theorem 3.4 (P025_body.tex:308-311, the cited coefficient bound) as a hypothesis type; it is the
type of `Sheil.Cited.coef_half_max` with `ZerosOnCircle` and `maxMod` unfolded (definitionally equal). -/
def HypCoef : Prop :=
  ∀ (P : ℂ[X]), 1 ≤ P.natDegree → ZerosOnCircle P → ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2

/-! ### `M ≥ 2A` in coefficient form (abstract, P025_body.tex:21-22) -/

/-- Row `abs_M_two_A_iff`. -/
theorem abs_M_two_A_iff_proved (P : ℂ[X]) :
    2 * coefMaxDeg P ≤ maxMod P ↔ ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2 := by
  have h1 : 2 * coefMaxDeg P ≤ maxMod P ↔ coefMaxDeg P ≤ maxMod P / 2 := by
    constructor <;> intro h <;> linarith
  rw [h1]
  unfold coefMaxDeg coefMax
  rw [Finset.sup'_le_iff]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-! ### The classes satisfy (eq:mirror) (Figure 1, Lemma 2.1) -/

/-- A self-inversive polynomial satisfies (eq:mirror) with `n = deg P`. -/
theorem mirror_of_selfInversive {P : ℂ[X]} (hP : SelfInversive P) : Mirror P.natDegree P := by
  obtain ⟨-, lam, hlam, hst⟩ := hP
  intro k hk
  have h := congrArg (fun Q => Q.coeff k) hst
  simp only [coeff_pstar, hk, ite_true, coeff_C_mul] at h
  have h2 := congrArg norm h
  rw [norm_mul, hlam, one_mul] at h2
  simpa using h2.symm

/-- A polynomial with `a_{n-k} = ±a_k` satisfies (eq:mirror). -/
theorem mirror_of_plusMinus {n : ℕ} {P : ℂ[X]} (hP : PlusMinusPalindromic n P) : Mirror n P := by
  obtain ⟨eps, heps, h⟩ := hP
  have he : ‖eps‖ = 1 := by rcases heps with rfl | rfl <;> simp
  intro k hk
  rw [h k hk, norm_mul, he, one_mul]

/-- Row `fig1_inclusions`. -/
theorem fig1_inclusions_proved :
    (∀ P : ℂ[X], SelfInversive P → Mirror P.natDegree P) ∧
    (∀ P : ℂ[X], PlusMinusPalindromic P.natDegree P → Mirror P.natDegree P) ∧
    (∀ P : ℂ[X], 1 ≤ P.natDegree → ZerosOnCircle P → SelfInversive P) :=
  ⟨fun _ hP => mirror_of_selfInversive hP, fun _ hP => mirror_of_plusMinus hP,
    fun P h1 hz => lem_2_1_circle_proved P h1 hz⟩

/-! ### The abstract's classes, from Theorem 4.1 with `n = deg P` -/

theorem abs_of_mirror (hthm : HypThm41) (P : ℂ[X]) (h1 : 1 ≤ P.natDegree) (hmir : Mirror P.natDegree P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P :=
  hthm P.natDegree h1 P le_rfl (by omega) hmir

/-- Row `abs_self_inversive`. -/
theorem abs_self_inversive_of (hthm : HypThm41) (P : ℂ[X]) (hP : SelfInversive P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P :=
  abs_of_mirror hthm P hP.1 (mirror_of_selfInversive hP)

/-- Row `abs_zeros_conj_inv`. -/
theorem abs_zeros_conj_inv_of (hthm : HypThm41) (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (h0 : P.eval 0 ≠ 0)
    (hsym : ZerosSymmConjInv P) : ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P :=
  abs_of_mirror hthm P hdeg (lem_2_1_mirror_proved P.natDegree P rfl h0 (Or.inl hsym))

/-- Row `abs_zeros_inv`. -/
theorem abs_zeros_inv_of (hthm : HypThm41) (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (h0 : P.eval 0 ≠ 0)
    (hsym : ZerosSymmInv P) : ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P :=
  abs_of_mirror hthm P hdeg (lem_2_1_mirror_proved P.natDegree P rfl h0 (Or.inr hsym))

/-- Row `abs_plus_minus`. -/
theorem abs_plus_minus_of (hthm : HypThm41) (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree)
    (hP : PlusMinusPalindromic P.natDegree P) : ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P :=
  abs_of_mirror hthm P hdeg (mirror_of_plusMinus hP)

/-! ### The normalization `λ = 1` (P025_body.tex:48-49) -/

theorem conj_mul_self_of_norm_one {mu : ℂ} (hmu : ‖mu‖ = 1) : conj mu * mu = 1 := by
  rw [Complex.conj_mul', hmu]
  simp

/-- Row `intro_normalize_lambda`. -/
theorem intro_normalize_lambda_proved (n : ℕ) (P : ℂ[X]) :
    (∃ lam : ℂ, ‖lam‖ = 1 ∧ pstar n P = C lam * P) ↔
      ∃ mu : ℂ, ‖mu‖ = 1 ∧ pstar n (C mu * P) = C mu * P := by
  constructor
  · rintro ⟨lam, hlam, hst⟩
    obtain ⟨mu, hsq⟩ := IsAlgClosed.exists_pow_nat_eq lam (by norm_num : 0 < 2)
    have hmu : ‖mu‖ = 1 := by
      have h := congrArg norm hsq
      rw [norm_pow, hlam] at h
      have h0 : 0 ≤ ‖mu‖ := norm_nonneg mu
      nlinarith [h]
    have hcm := conj_mul_self_of_norm_one hmu
    refine ⟨mu, hmu, ?_⟩
    rw [pstar_C_mul, hst, ← mul_assoc, ← C_mul]
    congr 2
    rw [← hsq]
    linear_combination mu * hcm
  · rintro ⟨mu, hmu, hst⟩
    rw [pstar_C_mul] at hst
    have hcm := conj_mul_self_of_norm_one hmu
    refine ⟨mu ^ 2, by rw [norm_pow, hmu, one_pow], ?_⟩
    calc pstar n P = C (conj mu * mu) * pstar n P := by rw [hcm, C_1, one_mul]
      _ = C mu * (C (conj mu) * pstar n P) := by rw [C_mul, mul_comm (C (conj mu)) (C mu), mul_assoc]
      _ = C mu * (C mu * P) := by rw [hst]
      _ = C (mu ^ 2) * P := by rw [← mul_assoc, ← C_mul, sq]

/-! ### `P(𝔻)` is a domain (abstract, P025_body.tex:15-16) -/

/-- Row `abs_domain`: open (open mapping theorem) and connected (continuous image of the disc). -/
theorem abs_domain_proved (P : ℂ[X]) (hnc : 0 < P.natDegree) :
    IsOpen (discImage P) ∧ IsConnected (discImage P) := by
  have hconn : IsConnected unitDisc :=
    (convex_ball (0 : ℂ) 1).isConnected (Metric.nonempty_ball.mpr one_pos)
  have han : AnalyticOnNhd ℂ (fun z => P.eval z) unitDisc :=
    fun z _ => (Polynomial.differentiable P).analyticAt z
  refine ⟨?_, hconn.image _ P.continuous.continuousOn⟩
  rcases han.is_constant_or_isOpen hconn.isPreconnected with ⟨w, hw⟩ | hopen
  · exfalso
    have hinf : Set.Infinite {x : ℂ | P.eval x = (C w).eval x} := by
      refine Set.Infinite.mono (fun x hx => ?_) (infinite_of_mem_nhds (0 : ℂ)
        (Metric.ball_mem_nhds (0 : ℂ) one_pos))
      simpa using hw x hx
    have hPC : P = C w := Polynomial.eq_of_infinite_eval_eq P (C w) hinf
    rw [hPC, natDegree_C] at hnc
    exact lt_irrefl 0 hnc
  · exact hopen unitDisc subset_rfl Metric.isOpen_ball

/-! ### Corollary 3.5 and the equivalences (Theorem 3.1 + Theorem 3.4) -/

/-- For `P` with all zeros on the circle: a disc of radius `A` in `P(𝔻)` iff `|a_k| ≤ M/2` for every `k`
(Theorem 3.1's last clause and `abs_M_two_A_iff`). -/
theorem cov_iff_coef (h31 : Hyp31) (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) :
    (∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔ ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2 := by
  obtain ⟨ζ, hζ, hM⟩ := Proofs.exists_max_circle_proved P
  exact (h31 P hdeg hz ζ hζ hM).2.2.trans (abs_M_two_A_iff_proved P)

/-- Row `cor_3_5` (P025_body.tex:321-323): Theorem 3.1 with Theorem 3.4, the cited result taken as the hypothesis
`hcoef`; Statements passes Sheil.Cited.coef_half_max. -/
theorem cor_3_5_of (h31 : Hyp31) (hcoef : HypCoef) (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P :=
  (cov_iff_coef h31 P hdeg hz).mpr (hcoef P hdeg hz)

/-- Row `intro_covering_implies_coef` (P025_body.tex:127-129): no cited input. -/
theorem intro_covering_implies_coef_of (h31 : Hyp31)
    (hcov : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q → ∃ c : ℂ, Metric.ball c (coefMaxDeg Q) ⊆ discImage Q) :
    ∀ P : ℂ[X], 1 ≤ P.natDegree → ZerosOnCircle P → ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2 :=
  fun P hdeg hz => (cov_iff_coef h31 P hdeg hz).mp (hcov P hdeg hz)

/-- Row `rem_4_2_equiv` (P025_body.tex:393-395): no cited input. -/
theorem rem_4_2_equiv_of (h31 : Hyp31) (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) :
    ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔
      ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2) ∧
    ((∀ k ≤ P.natDegree, 2 * k ≠ P.natDegree → ‖P.coeff k‖ ≤ maxMod P / 2) →
      ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔
        ∀ k : ℕ, 2 * k = P.natDegree → ‖P.coeff k‖ ≤ maxMod P / 2)) := by
  have hiff := cov_iff_coef h31 P hdeg hz
  refine ⟨hiff, fun hoff => hiff.trans ⟨fun hall k hk => hall k (by omega), fun hmid k hk => ?_⟩⟩
  by_cases h2 : 2 * k = P.natDegree
  · exact hmid k h2
  · exact hoff k hk h2

/-! ### Remark 4.2: `[OR74, Theorem 3]` (`k ≠ n/2`) suffices when `A` is attained off the middle -/

/-- The normalized step: `SelOK` for `Q` from a maximal index `j` with `2j ≠ n` and the bound for `k ≠ n/2`. -/
theorem selOK_of_off_middle (hPSD : HypPSD) (h31 : Hyp31)
    (hOR : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q →
      ∀ k ≤ Q.natDegree, 2 * k ≠ Q.natDegree → ‖Q.coeff k‖ ≤ maxMod Q / 2)
    {n : ℕ} (hn : 1 ≤ n) {Q : ℂ[X]} (hdeg : Q.natDegree ≤ n) (hmir : Mirror n Q) (h0 : Q.coeff 0 = 1)
    (hn1 : Q.coeff n = 1) {j : ℕ} (hjn : j ≤ n) (hj2 : 2 * j ≠ n) (hjA : ‖Q.coeff j‖ = coefMax n Q) :
    SelOK n Q := by
  intro hA
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [h0, norm_one] at hjA
    linarith
  have hjn' : j ≠ n := by
    rintro rfl
    rw [hn1, norm_one] at hjA
    linarith
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
  have hjn1 : j ≤ n - 1 := by omega
  refine ⟨j, hj1, hjn1, hjA, fun hw => ?_⟩
  obtain ⟨hHdeg, -, -, hcirc, hcoef, -⟩ := thm_4_1_wstar_of hPSD n hn Q hdeg hmir h0 hn1 hA j hj1 hjn1 hjA hw
  set H := Q - C (1 - Q.coeff (n - j) / conj (Q.coeff j)) with hH
  have hH1 : 1 ≤ H.natDegree := by rw [hHdeg]; exact hn
  have hHj : H.coeff j = Q.coeff j := coeff_sub_C_of_ne hj0
  have hbound := hOR H hH1 hcirc j (by rw [hHdeg]; exact hjn) (by rw [hHdeg]; exact hj2)
  have h2A : 2 * coefMaxDeg H ≤ maxMod H := by
    rw [hcoef, ← hjA, ← hHj]
    linarith
  obtain ⟨ζ, hζ, hM⟩ := Proofs.exists_max_circle_proved H
  obtain ⟨c, hc⟩ := (h31 H hH1 hcirc ζ hζ hM).2.2.mpr h2A
  rw [hcoef] at hc
  exact ⟨_, ball_of_ball_sub hc⟩

/-- Row `rem_4_2_off_middle` (P025_body.tex:391-392): no cited input; the hypothesis `hOR` is [OR74, Thm 3]
(or [SS74, Thm 3]: the same bound for `k ≠ n/2`). -/
theorem rem_4_2_off_middle_of (hPSD : HypPSD) (h31 : Hyp31)
    (hOR : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q →
      ∀ k ≤ Q.natDegree, 2 * k ≠ Q.natDegree → ‖Q.coeff k‖ ≤ maxMod Q / 2)
    (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree) (hmir : Mirror n P)
    (hj : ∃ j ≤ n, 2 * j ≠ n ∧ ‖P.coeff j‖ = coefMax n P) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P := by
  obtain ⟨j, hjn, hj2, hjA⟩ := hj
  refine cover_of_sel hPSD n hn P hdeg hnc hmir (fun h0 alpha ha hpow => ?_)
  obtain ⟨hQ0, hQn, hQdeg, hQmir, -, hQA, -⟩ := (thm_4_1_normalize_of n hn P hdeg hmir h0).2.2.2 alpha ha hpow
  refine selOK_of_off_middle hPSD h31 hOR hn hQdeg hQmir hQ0 hQn hjn hj2 ?_
  rw [norm_coeff_normalizeAt P ha, hQA, hjA]

/-- From "not (`n` even and `|a_{n/2}|` strictly largest)": a maximal index `j` with `2j ≠ n`. -/
theorem exists_off_middle {n : ℕ} {P : ℂ[X]}
    (hnot : ¬ (Even n ∧ ∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖)) :
    ∃ j ≤ n, 2 * j ≠ n ∧ ‖P.coeff j‖ = coefMax n P := by
  obtain ⟨k0, hk0, hA⟩ := exists_coefMax n P
  by_cases h2 : 2 * k0 = n
  · have hev : Even n := ⟨k0, by omega⟩
    have hk0' : n / 2 = k0 := by omega
    have hnall : ¬ ∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖ := fun h => hnot ⟨hev, h⟩
    push Not at hnall
    obtain ⟨k, hk, hne, hge⟩ := hnall
    rw [hk0', hA] at hge
    exact ⟨k, hk, by omega, le_antisymm (le_coefMax P hk) hge⟩
  · exact ⟨k0, hk0, h2, hA⟩

/-- Row `rem_4_2_middle_only` (P025_body.tex:392-393): no cited input. -/
theorem rem_4_2_middle_only_of (hPSD : HypPSD) (h31 : Hyp31)
    (hOR : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q →
      ∀ k ≤ Q.natDegree, 2 * k ≠ Q.natDegree → ‖Q.coeff k‖ ≤ maxMod Q / 2)
    (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree) (hmir : Mirror n P)
    (hnot : ¬ (Even n ∧ ∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖)) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P :=
  rem_4_2_off_middle_of hPSD h31 hOR n hn P hdeg hnc hmir (exists_off_middle hnot)

/-! ### Remark 4.2: the four conditions under which the middle case is used (P025_body.tex:392-393) -/

/-- The middle coefficient is the maximum when it is strictly larger than every other one. -/
theorem coefMax_eq_middle {n : ℕ} {P : ℂ[X]}
    (hstrict : ∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖) :
    coefMax n P = ‖P.coeff (n / 2)‖ := by
  apply le_antisymm
  · obtain ⟨k, hk, hkA⟩ := exists_coefMax n P
    rw [← hkA]
    by_cases hkm : k = n / 2
    · rw [hkm]
    · exact (hstrict k hk hkm).le
  · exact le_coefMax P (Nat.div_le_self n 2)

/-- Row `rem_4_2_middle_used_only` (P025_body.tex:392-393): "the middle case of Theorem 3.4 ... is used only when `n`
is even, `|a_{n/2}|` is strictly larger than every other `|a_k|` and than `2|a_0|`, and `w_*` is omitted": unless all
four hold, Theorem 4.1 follows from the bound for `k ≠ n/2` alone (hypothesis `hOR`). `w_*` is the point `1 - E` of
the normalized `Q = P(αz)/a_0` with `j = n/2` (`E = q_{n-j}/conj(q_j)`); "`w_*` is omitted" is stated for every
admissible `α` (and needs `a_0 ≠ 0`: there is no `w_*` in Case 1). No cited input. -/
theorem rem_4_2_middle_used_only_of (hPSD : HypPSD) (h31 : Hyp31)
    (hOR : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q →
      ∀ k ≤ Q.natDegree, 2 * k ≠ Q.natDegree → ‖Q.coeff k‖ ≤ maxMod Q / 2)
    (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree) (hmir : Mirror n P)
    (hnot : ¬ (Even n ∧ (∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖) ∧
      2 * ‖P.coeff 0‖ < ‖P.coeff (n / 2)‖ ∧ P.coeff 0 ≠ 0 ∧
      ∀ alpha : ℂ, ‖alpha‖ = 1 → alpha ^ n = P.coeff 0 / P.coeff n →
        1 - (normalizeAt P alpha).coeff (n - n / 2) / conj ((normalizeAt P alpha).coeff (n / 2)) ∉
          discImage (normalizeAt P alpha))) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P := by
  by_cases hmid : Even n ∧ ∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖
  swap
  · exact rem_4_2_middle_only_of hPSD h31 hOR n hn P hdeg hnc hmir hmid
  obtain ⟨hev, hstrict⟩ := hmid
  have hA := coefMax_eq_middle hstrict
  by_cases h0 : P.coeff 0 = 0
  · exact rem_4_2_no_coef_of hPSD n hn P hdeg hnc hmir (Or.inl h0)
  by_cases hbig : 2 * ‖P.coeff 0‖ < ‖P.coeff (n / 2)‖
  swap
  · push Not at hbig
    exact rem_4_2_no_coef_of hPSD n hn P hdeg hnc hmir (Or.inr (by rw [hA]; exact hbig))
  have htaken : ∃ alpha : ℂ, ‖alpha‖ = 1 ∧ alpha ^ n = P.coeff 0 / P.coeff n ∧
      1 - (normalizeAt P alpha).coeff (n - n / 2) / conj ((normalizeAt P alpha).coeff (n / 2)) ∈
        discImage (normalizeAt P alpha) := by
    by_contra hcon
    push Not at hcon
    exact hnot ⟨hev, hstrict, hbig, h0, hcon⟩
  obtain ⟨alpha, ha, hpow, hw⟩ := htaken
  obtain ⟨hQ0, hQn, hQdeg, hQmir, hQimg, hQA, -⟩ := (thm_4_1_normalize_of n hn P hdeg hmir h0).2.2.2 alpha ha hpow
  have hpos : 0 < ‖P.coeff 0‖ := norm_pos_iff.mpr h0
  obtain ⟨r, hr⟩ := hev
  have hj1 : 1 ≤ n / 2 := by omega
  have hjn : n / 2 ≤ n - 1 := by omega
  have hjA : ‖(normalizeAt P alpha).coeff (n / 2)‖ = coefMax n (normalizeAt P alpha) := by
    rw [norm_coeff_normalizeAt P ha, hQA, hA]
  have hA1 : 1 < coefMax n (normalizeAt P alpha) := by
    rw [hQA, hA, lt_div_iff₀ hpos]
    linarith
  have hball := rem_4_2_wstar_taken_of hPSD n hn _ hQdeg hQmir hQ0 hQn hA1 (n / 2) hj1 hjn hjA hw
  rw [hQimg, hQA] at hball
  have := ball_of_ball_div h0 hball
  rw [div_mul_cancel₀ _ hpos.ne'] at this
  exact ⟨_, this⟩

/-! ### The idea of the proof: `D(1,1) ⊆ P(𝔻)` for every `A` (P025_body.tex:140-141) -/

/-- Row `sketch_disc_one` (P025_body.tex:140-141: "the diagonal entries `K_jj` all equal `|1-w|^2-1 ≥ 0`, so
`|1-w| ≥ 1`, which gives `D(1,1) ⊂ P(𝔻)`"): with `a_0 = a_n = 1`, every omitted `w` has `|1-w|^2 - 1 ≥ 0` and
`|1-w| ≥ 1`, and `D(1,1) ⊆ P(𝔻)` for EVERY `A` (one step from the second clause of `thm_4_1_case2_diag`). -/
theorem sketch_disc_one_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) :
    (∀ w ∉ discImage P, 0 ≤ ‖1 - w‖ ^ 2 - 1 ∧ 1 ≤ ‖1 - w‖) ∧ Metric.ball 1 1 ⊆ discImage P := by
  have homit := (thm_4_1_case2_diag_of hPSD n hn P hdeg hmir h0 hn1).2.1
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have h1 := homit w hw
    rw [norm_sub_rev] at h1
    exact ⟨by nlinarith [norm_nonneg (1 - w)], h1⟩
  · by_contra hcon
    have h1 := homit w hcon
    rw [Metric.mem_ball, dist_eq_norm] at hw
    linarith

/-! Axiom census of this file (run by the compile log). -/
#print axioms abs_M_two_A_iff_proved
#print axioms fig1_inclusions_proved
#print axioms abs_self_inversive_of
#print axioms intro_normalize_lambda_proved
#print axioms abs_domain_proved
#print axioms cor_3_5_of
#print axioms intro_covering_implies_coef_of
#print axioms rem_4_2_equiv_of
#print axioms rem_4_2_off_middle_of
#print axioms rem_4_2_middle_only_of
#print axioms sketch_disc_one_of
#print axioms rem_4_2_middle_used_only_of

end Sheil
