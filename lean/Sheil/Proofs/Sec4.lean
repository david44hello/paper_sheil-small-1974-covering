/- Sheil/Proofs/Sec4.lean — proofs of the rows thm_4_1_case1, eq_minor, eq_punctured, thm_4_1_case2_diag, thm_4_1_wstar, rem_4_2_wstar_taken and 4 more of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Proofs.Basic

namespace Sheil

open Polynomial ComplexConjugate
open scoped ComplexOrder

/-- The PSD half of Lemma 2.2(b), as a hypothesis type (proved in Sheil/Proofs/Lemma22.lean). -/
def HypPSD : Prop :=
  ∀ (n : ℕ) (H : ℂ[X]), H.natDegree ≤ n → (∀ z ∈ unitDisc, H.eval z ≠ 0) → (schurCohn n H).PosSemidef

/-! ### `coefMax` and the image -/

theorem le_coefMax {n k : ℕ} (P : ℂ[X]) (hk : k ≤ n) : ‖P.coeff k‖ ≤ coefMax n P :=
  Finset.le_sup' (fun k => ‖P.coeff k‖) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem exists_coefMax (n : ℕ) (P : ℂ[X]) : ∃ k ≤ n, ‖P.coeff k‖ = coefMax n P := by
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n + 1))
    Finset.nonempty_range_add_one (fun k => ‖P.coeff k‖)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), he.symm⟩

theorem coefMax_nonneg (n : ℕ) (P : ℂ[X]) : 0 ≤ coefMax n P :=
  le_trans (norm_nonneg _) (le_coefMax (n := n) (k := 0) P (Nat.zero_le n))

theorem coefMax_pos {n : ℕ} {P : ℂ[X]} (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree) : 0 < coefMax n P := by
  have hP : P ≠ 0 := by rintro rfl; simp at hnc
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  exact lt_of_lt_of_le (norm_pos_iff.mpr hlc) (le_coefMax P hdeg)

/-- `coefMax` depends only on the moduli of the coefficients `0..n`. -/
theorem coefMax_congr {n : ℕ} {P Q : ℂ[X]} (h : ∀ k ≤ n, ‖P.coeff k‖ = ‖Q.coeff k‖) :
    coefMax n P = coefMax n Q := by
  unfold coefMax
  exact Finset.sup'_congr _ rfl (fun k hk => h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))

theorem mem_discImage {P : ℂ[X]} {w : ℂ} : w ∈ discImage P ↔ ∃ z : ℂ, ‖z‖ < 1 ∧ P.eval z = w := by
  simp [discImage, unitDisc, Metric.mem_ball, dist_zero_right]

theorem coeff_zero_mem_discImage (P : ℂ[X]) : P.coeff 0 ∈ discImage P :=
  mem_discImage.mpr ⟨0, by simp, by simp [Polynomial.coeff_zero_eq_eval_zero]⟩

/-- An omitted value `w` makes `P - w` zero-free on the disc. -/
theorem omitted_noZero {P : ℂ[X]} {w : ℂ} (hw : w ∉ discImage P) :
    ∀ z ∈ unitDisc, (P - C w).eval z ≠ 0 := by
  intro z hz h
  apply hw
  refine mem_discImage.mpr ⟨z, ?_, ?_⟩
  · simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hz
  · simpa [sub_eq_zero] using h

theorem natDegree_sub_C_le {P : ℂ[X]} {n : ℕ} (hdeg : P.natDegree ≤ n) (w : ℂ) : (P - C w).natDegree ≤ n :=
  le_trans (natDegree_sub_le _ _) (max_le hdeg (by simp))

theorem coeff_sub_C_of_ne {P : ℂ[X]} {w : ℂ} {k : ℕ} (hk : k ≠ 0) : (P - C w).coeff k = P.coeff k := by
  simp [coeff_sub, coeff_C, hk]

/-! ### Entries of the Schur-Cohn matrix -/

/-- The first row: `K_{0j} = h_0 conj(h_j) - conj(h_n) h_{n-j}` (eq:entries). -/
theorem schurCohn_zero_left (n : ℕ) (H : ℂ[X]) (h0 : 0 < n) (j : Fin n) :
    schurCohn n H ⟨0, h0⟩ j = H.coeff 0 * conj (H.coeff j) - conj (H.coeff n) * H.coeff (n - j) := by
  simp [schurCohn]

/-- If `|h_k| = |h_{n-k}|` for `1 ≤ k ≤ n-1`, every diagonal entry is `|h_0|^2 - |h_n|^2` (P025_body.tex:349, 360). -/
theorem schurCohn_diag_of_mirror (n : ℕ) (H : ℂ[X])
    (hmid : ∀ k, 1 ≤ k → k + 1 ≤ n → ‖H.coeff k‖ = ‖H.coeff (n - k)‖) (j : Fin n) :
    schurCohn n H j j = ((‖H.coeff 0‖ ^ 2 - ‖H.coeff n‖ ^ 2 : ℝ) : ℂ) := by
  have hj := j.isLt
  unfold schurCohn
  rw [min_self, Finset.sum_range_succ]
  have hlast : (n - (j : ℕ) + j) = n := Nat.sub_add_cancel hj.le
  rw [Nat.sub_self, hlast]
  have hrest : ∑ r ∈ Finset.range (j : ℕ),
      (H.coeff ((j : ℕ) - r) * conj (H.coeff ((j : ℕ) - r)) -
        conj (H.coeff (n - (j : ℕ) + r)) * H.coeff (n - (j : ℕ) + r)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hr' : r < (j : ℕ) := Finset.mem_range.mp hr
    have hk1 : 1 ≤ (j : ℕ) - r := by omega
    have hk2 : (j : ℕ) - r + 1 ≤ n := by omega
    have hidx : n - ((j : ℕ) - r) = n - (j : ℕ) + r := by omega
    have hm := hmid ((j : ℕ) - r) hk1 hk2
    rw [hidx] at hm
    rw [Complex.mul_conj', Complex.conj_mul', hm, sub_self]
  rw [hrest, zero_add, Complex.mul_conj', Complex.conj_mul']
  push_cast
  ring

/-- For `P` with (eq:mirror) and `n ≥ 1`, `H = P - w` satisfies the hypothesis of `schurCohn_diag_of_mirror`. -/
theorem mirror_mid_sub_C {n : ℕ} {P : ℂ[X]} (hmir : Mirror n P) (w : ℂ) :
    ∀ k, 1 ≤ k → k + 1 ≤ n → ‖(P - C w).coeff k‖ = ‖(P - C w).coeff (n - k)‖ := by
  intro k hk1 hk2
  rw [coeff_sub_C_of_ne (by omega), coeff_sub_C_of_ne (by omega)]
  exact hmir k (by omega)

/-- The `2 × 2` minor on the indices `0, j` when `K_{00} = K_{jj} = d` (real). -/
theorem minor_zero_j {n : ℕ} {K : Matrix (Fin n) (Fin n) ℂ} (hK : K.PosSemidef) (h0 : 0 < n) (j : Fin n) (d : ℝ)
    (hd0 : K ⟨0, h0⟩ ⟨0, h0⟩ = (d : ℂ)) (hdj : K j j = (d : ℂ)) : 0 ≤ d ∧ ‖K ⟨0, h0⟩ j‖ ≤ d := by
  have hnn : 0 ≤ d := by
    have := hK.diag_nonneg (i := ⟨0, h0⟩)
    rw [hd0] at this
    exact_mod_cast this
  refine ⟨hnn, ?_⟩
  have hm := psd_minor hK ⟨0, h0⟩ j
  rw [hd0, hdj, Complex.ofReal_re] at hm
  have : ‖K ⟨0, h0⟩ j‖ ^ 2 ≤ d ^ 2 := by nlinarith
  nlinarith [norm_nonneg (K ⟨0, h0⟩ j)]

/-! ### Case 1: `a_0 = 0` (P025_body.tex:346-353) -/

/-- Case 1, the omitted-value bound: every omitted `w` is non-zero and has `|w| ≥ |a_j|` for `1 ≤ j ≤ n-1`. -/
theorem case1_omitted (hPSD : HypPSD) {n : ℕ} (hn : 1 ≤ n) {P : ℂ[X]} (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 0) {w : ℂ} (hw : w ∉ discImage P) {j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) : w ≠ 0 ∧ ‖P.coeff j‖ ≤ ‖w‖ := by
  have hw0 : w ≠ 0 := by
    rintro rfl; exact hw (h0 ▸ coeff_zero_mem_discImage P)
  refine ⟨hw0, ?_⟩
  have hn0 : 0 < n := by omega
  have han : P.coeff n = 0 := by
    have := hmir 0 (Nat.zero_le n); rw [h0, Nat.sub_zero, norm_zero] at this
    exact norm_eq_zero.mp this.symm
  set H := P - C w with hH
  have hK := hPSD n H (natDegree_sub_C_le hdeg w) (omitted_noZero hw)
  have hdiag := schurCohn_diag_of_mirror n H (mirror_mid_sub_C hmir w)
  have hH0 : H.coeff 0 = -w := by simp [hH, h0]
  have hHn : H.coeff n = 0 := by rw [hH, coeff_sub_C_of_ne (by omega), han]
  have hHj : H.coeff j = P.coeff j := by rw [hH, coeff_sub_C_of_ne (by omega)]
  have hHnj : H.coeff (n - j) = P.coeff (n - j) := by rw [hH, coeff_sub_C_of_ne (by omega)]
  have hd : ∀ i : Fin n, schurCohn n H i i = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    intro i; rw [hdiag i, hH0, hHn]; simp
  obtain ⟨-, hle⟩ := minor_zero_j hK hn0 ⟨j, by omega⟩ (‖w‖ ^ 2) (hd _) (hd _)
  rw [schurCohn_zero_left] at hle
  simp only [hH0, hHn, hHj, hHnj, map_zero, zero_mul, sub_zero] at hle
  rw [norm_mul, norm_neg, Complex.norm_conj] at hle
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  nlinarith

/-- Case 1 (P025_body.tex:346-353), all its claims. -/
theorem thm_4_1_case1_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hnc : 0 < P.natDegree) (hmir : Mirror n P) (h0 : P.coeff 0 = 0) :
    P.coeff n = 0 ∧ 2 ≤ n ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 1 ∧ ‖P.coeff j‖ = coefMax n P) ∧
    (∀ w ∉ discImage P, w ≠ 0 ∧ coefMax n P ≤ ‖w‖) ∧ Metric.ball 0 (coefMax n P) ⊆ discImage P := by
  have han : P.coeff n = 0 := by
    have := hmir 0 (Nat.zero_le n); rw [h0, Nat.sub_zero, norm_zero] at this
    exact norm_eq_zero.mp this.symm
  have hApos := coefMax_pos hdeg hnc
  obtain ⟨j, hjn, hjA⟩ := exists_coefMax n P
  have hj0 : j ≠ 0 := by rintro rfl; rw [h0, norm_zero] at hjA; linarith
  have hjn' : j ≠ n := by rintro rfl; rw [han, norm_zero] at hjA; linarith
  have hj : ∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 1 ∧ ‖P.coeff j‖ = coefMax n P := ⟨j, by omega, by omega, hjA⟩
  have hn2 : 2 ≤ n := by omega
  have hom : ∀ w ∉ discImage P, w ≠ 0 ∧ coefMax n P ≤ ‖w‖ := by
    intro w hw
    obtain ⟨hw0, hle⟩ := case1_omitted hPSD hn hdeg hmir h0 hw (j := j) (by omega) (by omega)
    exact ⟨hw0, hjA ▸ hle⟩
  refine ⟨han, hn2, hj, hom, ?_⟩
  intro w hw
  by_contra hnot
  have := (hom w hnot).2
  rw [Metric.mem_ball, dist_zero_right] at hw
  linarith

/-! ### Case 2 after the normalization `a_0 = a_n = 1` (P025_body.tex:359-385) -/

/-- The diagonal: `K_{jj} = |1 - w|^2 - 1` for `H = P - w`, every `w` and `j` (P025_body.tex:359-362). -/
theorem case2_diag {n : ℕ} (hn : 1 ≤ n) {P : ℂ[X]} (hmir : Mirror n P) (h0 : P.coeff 0 = 1)
    (hn1 : P.coeff n = 1) (w : ℂ) (j : Fin n) :
    schurCohn n (P - C w) j j = ((‖1 - w‖ ^ 2 - 1 : ℝ) : ℂ) := by
  rw [schurCohn_diag_of_mirror n _ (mirror_mid_sub_C hmir w) j]
  have h0' : (P - C w).coeff 0 = 1 - w := by simp [h0]
  rw [h0', coeff_sub_C_of_ne (by omega), hn1]
  simp

/-- An omitted value `w` (normalized `P`): `|w - 1| ≥ 1`, and for `1 ≤ j ≤ n-1`, with `E = a_{n-j}/conj(a_j)`,
`|a_j| |(w - 1) + E| ≤ |w - 1|^2 - 1` (the `2 × 2` minor, P025_body.tex:362-372). -/
theorem case2_omitted (hPSD : HypPSD) {n : ℕ} (hn : 1 ≤ n) {P : ℂ[X]} (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) {w : ℂ} (hw : w ∉ discImage P) :
    1 ≤ ‖w - 1‖ ∧ ∀ j : ℕ, 1 ≤ j → j + 1 ≤ n →
      ‖P.coeff j‖ * ‖(w - 1) + P.coeff (n - j) / conj (P.coeff j)‖ ≤ ‖w - 1‖ ^ 2 - 1 := by
  have hn0 : 0 < n := by omega
  have hK := hPSD n (P - C w) (natDegree_sub_C_le hdeg w) (omitted_noZero hw)
  have hd := case2_diag hn hmir h0 hn1 w
  have hnorm : ‖1 - w‖ = ‖w - 1‖ := norm_sub_rev 1 w
  obtain ⟨hdnn, -⟩ := minor_zero_j hK hn0 ⟨0, hn0⟩ _ (hd _) (hd _)
  refine ⟨?_, ?_⟩
  · rw [hnorm] at hdnn; nlinarith [norm_nonneg (w - 1)]
  intro j hj1 hjn
  obtain ⟨-, hle⟩ := minor_zero_j hK hn0 ⟨j, by omega⟩ _ (hd _) (hd _)
  rw [schurCohn_zero_left] at hle
  have hc0 : (P - C w).coeff 0 = 1 - w := by simp [h0]
  have hcn : (P - C w).coeff n = 1 := by rw [coeff_sub_C_of_ne (by omega), hn1]
  have hcj : (P - C w).coeff j = P.coeff j := coeff_sub_C_of_ne (by omega)
  have hcnj : (P - C w).coeff (n - j) = P.coeff (n - j) := coeff_sub_C_of_ne (by omega)
  simp only [hc0, hcn, hcj, hcnj, map_one, one_mul] at hle
  rw [hnorm] at hle
  by_cases haj : P.coeff j = 0
  · rw [haj, norm_zero, zero_mul]; rw [hnorm] at hdnn; exact hdnn
  · have hcj0 : conj (P.coeff j) ≠ 0 := by simpa using haj
    have hid : (1 - w) * conj (P.coeff j) - P.coeff (n - j) =
        -(conj (P.coeff j) * ((w - 1) + P.coeff (n - j) / conj (P.coeff j))) := by
      field_simp; ring
    rw [hid, norm_neg, norm_mul, Complex.norm_conj] at hle
    exact hle

/-- `|u|^2 - |E|^2 ≤ |u + E| |u - E|`. -/
theorem sq_sub_le_mul (u E : ℂ) : ‖u‖ ^ 2 - ‖E‖ ^ 2 ≤ ‖u + E‖ * ‖u - E‖ := by
  rw [← norm_mul, show (u + E) * (u - E) = u ^ 2 - E ^ 2 by ring, ← norm_pow, ← norm_pow]
  exact norm_sub_norm_le _ _

/-- Eq. (eq:minor), P025_body.tex:367-372 (row `eq_minor`). -/
theorem eq_minor_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 1 ∧ ‖P.coeff j‖ = coefMax n P) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ‖P.coeff j‖ = coefMax n P →
      ‖P.coeff (n - j) / conj (P.coeff j)‖ = 1 ∧
      ∀ w ∉ discImage P,
        coefMax n P * ‖(w - 1) + P.coeff (n - j) / conj (P.coeff j)‖ ≤ ‖w - 1‖ ^ 2 - 1 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hkn, hkA⟩ := exists_coefMax n P
    have hk0 : k ≠ 0 := by rintro rfl; rw [h0, norm_one] at hkA; linarith
    have hkn' : k ≠ n := by rintro rfl; rw [hn1, norm_one] at hkA; linarith
    exact ⟨k, by omega, by omega, hkA⟩
  · intro j hj1 hjn hjA
    have hjpos : 0 < ‖P.coeff j‖ := by rw [hjA]; linarith
    refine ⟨?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, ← hmir j (by omega)]
      exact div_self hjpos.ne'
    · intro w hw
      have := (case2_omitted hPSD hn hdeg hmir h0 hn1 hw).2 j hj1 (by omega)
      rwa [hjA] at this

/-- Eq. (eq:punctured), P025_body.tex:373-378 (row `eq_punctured`). -/
theorem eq_punctured_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) (hjA : ‖P.coeff j‖ = coefMax n P) :
    Metric.ball (1 + P.coeff (n - j) / conj (P.coeff j)) (coefMax n P) \
      {1 - P.coeff (n - j) / conj (P.coeff j)} ⊆ discImage P := by
  set E := P.coeff (n - j) / conj (P.coeff j) with hE
  obtain ⟨-, hall⟩ := eq_minor_of hPSD n hn P hdeg hmir h0 hn1 hA
  obtain ⟨hE1, hmin⟩ := hall j hj1 hjn hjA
  rintro w ⟨hwb, hwne⟩
  by_contra hw
  have h1 := hmin w hw
  have h2 := sq_sub_le_mul (w - 1) E
  rw [hE1] at h2
  have hne : (w - 1) + E ≠ 0 := by
    intro h; apply hwne; rw [Set.mem_singleton_iff]; linear_combination h
  have hpos : 0 < ‖(w - 1) + E‖ := norm_pos_iff.mpr hne
  have h3 : coefMax n P ≤ ‖w - 1 - E‖ := by
    have : coefMax n P * ‖(w - 1) + E‖ ≤ ‖w - 1 - E‖ * ‖(w - 1) + E‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  rw [Metric.mem_ball, dist_eq_norm, show w - (1 + E) = w - 1 - E by ring] at hwb
  linarith

/-- The case `A = 1` (P025_body.tex:364-365): `D(1,1) ⊆ P(𝔻)`. -/
theorem case2_A_one (hPSD : HypPSD) {n : ℕ} (hn : 1 ≤ n) {P : ℂ[X]} (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) : Metric.ball 1 1 ⊆ discImage P := by
  intro w hw
  by_contra hw'
  have := (case2_omitted hPSD hn hdeg hmir h0 hn1 hw').1
  rw [Metric.mem_ball, dist_eq_norm] at hw
  linarith

/-- Theorem 4.1, Case 2 diagonal step (row `thm_4_1_case2_diag`). -/
theorem thm_4_1_case2_diag_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) :
    (∀ w : ℂ, ∀ j : Fin n, schurCohn n (P - C w) j j = ((‖1 - w‖ ^ 2 - 1 : ℝ) : ℂ)) ∧
    (∀ w ∉ discImage P, 1 ≤ ‖w - 1‖) ∧
    (coefMax n P = 1 → Metric.ball 1 1 ⊆ discImage P) :=
  ⟨case2_diag hn hmir h0 hn1, fun _ hw => (case2_omitted hPSD hn hdeg hmir h0 hn1 hw).1,
    fun _ => case2_A_one hPSD hn hdeg hmir h0 hn1⟩

/-! ### The exceptional value `w_*` (P025_body.tex:380-385) -/

theorem one_le_multiset_prod (s : Multiset ℝ) (h1 : ∀ x ∈ s, 1 ≤ x) : 1 ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons]
    have ha := h1 a (Multiset.mem_cons_self a t)
    have ht := ih (fun y hy => h1 y (Multiset.mem_cons_of_mem hy))
    nlinarith

theorem eq_one_of_multiset_prod (s : Multiset ℝ) (h1 : ∀ x ∈ s, 1 ≤ x) (hp : s.prod = 1) :
    ∀ x ∈ s, x = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    intro x hx
    have ha := h1 a (Multiset.mem_cons_self a t)
    have ht1 : ∀ y ∈ t, 1 ≤ y := fun y hy => h1 y (Multiset.mem_cons_of_mem hy)
    have htp := one_le_multiset_prod t ht1
    rw [Multiset.prod_cons] at hp
    have ha1 : a = 1 := by nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 htp)]
    have htp1 : t.prod = 1 := by rw [ha1, one_mul] at hp; exact hp
    rcases Multiset.mem_cons.mp hx with rfl | hxt
    · exact ha1
    · exact ih ht1 htp1 x hxt

/-- A monic polynomial with no zero in `𝔻` and `|H(0)| = 1` has all its zeros on the unit circle
(P025_body.tex:381-382: "its n zeros have modulus at least 1, while their product has modulus |E| = 1"). -/
theorem zerosOnCircle_of_monic {H : ℂ[X]} (hmon : H.Monic) (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0)
    (h0 : ‖H.coeff 0‖ = 1) : ZerosOnCircle H := by
  have hH0 : H ≠ 0 := hmon.ne_zero
  have hfac : H = (H.roots.map (fun a => X - C a)).prod := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := H))
    rw [hmon.leadingCoeff, C_1, one_mul] at this
    exact this.symm
  have hge : ∀ r ∈ H.roots, 1 ≤ ‖r‖ := by
    intro r hr
    by_contra hlt
    push Not at hlt
    exact hD r (by simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hlt)
      ((mem_roots hH0).mp hr)
  have hprod : (H.roots.map (fun r => ‖r‖)).prod = 1 := by
    have he : H.coeff 0 = (H.roots.map (fun a => -a)).prod := by
      rw [coeff_zero_eq_eval_zero]
      conv_lhs => rw [hfac]
      rw [eval_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro a _
      simp
    have key : ∀ s : Multiset ℂ, ‖(s.map (fun a => -a)).prod‖ = (s.map (fun a => ‖a‖)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a t ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_neg, ih, Multiset.map_cons,
          Multiset.prod_cons]
    rw [he, key] at h0
    exact h0
  have hall := eq_one_of_multiset_prod _ (fun x hx => by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact hge r hr) hprod
  intro z hz
  exact hall ‖z‖ (Multiset.mem_map_of_mem _ ((mem_roots hH0).mpr hz))

/-- Row `thm_4_1_wstar` (P025_body.tex:380-385). -/
theorem thm_4_1_wstar_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) (hjA : ‖P.coeff j‖ = coefMax n P)
    (hw : 1 - P.coeff (n - j) / conj (P.coeff j) ∉ discImage P) :
    (P - C (1 - P.coeff (n - j) / conj (P.coeff j))).natDegree = n ∧
    (P - C (1 - P.coeff (n - j) / conj (P.coeff j))).coeff 0 = P.coeff (n - j) / conj (P.coeff j) ∧
    (P - C (1 - P.coeff (n - j) / conj (P.coeff j))).coeff n = 1 ∧
    ZerosOnCircle (P - C (1 - P.coeff (n - j) / conj (P.coeff j))) ∧
    coefMaxDeg (P - C (1 - P.coeff (n - j) / conj (P.coeff j))) = coefMax n P ∧
    discImage P = (fun w => w + (1 - P.coeff (n - j) / conj (P.coeff j))) ''
      discImage (P - C (1 - P.coeff (n - j) / conj (P.coeff j))) := by
  set E := P.coeff (n - j) / conj (P.coeff j) with hE
  set H := P - C (1 - E) with hH
  have hE1 : ‖E‖ = 1 := ((eq_minor_of hPSD n hn P hdeg hmir h0 hn1 hA).2 j hj1 hjn hjA).1
  have hHn : H.coeff n = 1 := by rw [hH, coeff_sub_C_of_ne (by omega), hn1]
  have hH0 : H.coeff 0 = E := by simp [hH, h0]
  have hHdeg : H.natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_sub_C_le hdeg _) (by rw [hHn]; exact one_ne_zero)
  have hmon : H.Monic := by rw [Monic, leadingCoeff, hHdeg, hHn]
  have hcirc : ZerosOnCircle H := zerosOnCircle_of_monic hmon (omitted_noZero hw) (by rw [hH0, hE1])
  have hcoef : coefMaxDeg H = coefMax n P := by
    unfold coefMaxDeg; rw [hHdeg]
    apply coefMax_congr
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; rw [hH0, hE1, h0, norm_one]
    · rw [hH, coeff_sub_C_of_ne hk0]
  have himg : discImage P = (fun w => w + (1 - E)) '' discImage H := by
    ext w
    simp only [mem_discImage, Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨H.eval z, ⟨z, hz, rfl⟩, by simp [hH]⟩
    · rintro ⟨v, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by simp [hH]⟩
  exact ⟨hHdeg, hH0, hHn, hcirc, hcoef, himg⟩

/-- Row `rem_4_2_wstar_taken` (P025_body.tex:380, 388-390): if `w_*` is taken, `D(1+E, A) ⊆ P(𝔻)`. -/
theorem rem_4_2_wstar_taken_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) (hjA : ‖P.coeff j‖ = coefMax n P)
    (hw : 1 - P.coeff (n - j) / conj (P.coeff j) ∈ discImage P) :
    Metric.ball (1 + P.coeff (n - j) / conj (P.coeff j)) (coefMax n P) ⊆ discImage P := by
  intro w hwb
  by_cases hwe : w = 1 - P.coeff (n - j) / conj (P.coeff j)
  · exact hwe ▸ hw
  · exact eq_punctured_of hPSD n hn P hdeg hmir h0 hn1 hA j hj1 hjn hjA ⟨hwb, hwe⟩

/-- Row `rem_4_2_dist` (P025_body.tex:388-389). -/
theorem rem_4_2_dist_of (E : ℂ) (hE : ‖E‖ = 1) (A : ℝ) :
    ‖(1 - E) - (1 + E)‖ = 2 ∧ ((1 - E) ∈ Metric.ball (1 + E) A ↔ 2 < A) := by
  have h2 : ‖(1 - E) - (1 + E)‖ = 2 := by
    rw [show (1 - E) - (1 + E) = -(2 * E) by ring, norm_neg, norm_mul, hE]; norm_num
  refine ⟨h2, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, h2]

/-! ### The normalization (P025_body.tex:355-357) and the assembly -/

theorem coeff_normalizeAt (P : ℂ[X]) (alpha : ℂ) (k : ℕ) :
    (normalizeAt P alpha).coeff k = (P.coeff 0)⁻¹ * (P.coeff k * alpha ^ k) := by
  simp [normalizeAt, coeff_C_mul]

theorem eval_normalizeAt (P : ℂ[X]) (alpha z : ℂ) :
    (normalizeAt P alpha).eval z = (P.coeff 0)⁻¹ * P.eval (alpha * z) := by
  simp [normalizeAt, eval_comp]

theorem norm_coeff_normalizeAt (P : ℂ[X]) {alpha : ℂ} (ha : ‖alpha‖ = 1) (k : ℕ) :
    ‖(normalizeAt P alpha).coeff k‖ = ‖P.coeff k‖ / ‖P.coeff 0‖ := by
  rw [coeff_normalizeAt, norm_mul, norm_inv, norm_mul, norm_pow, ha, one_pow, mul_one, inv_mul_eq_div]

/-- Row `thm_4_1_normalize` (P025_body.tex:355-357). -/
theorem thm_4_1_normalize_of (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 ≠ 0) :
    P.coeff n ≠ 0 ∧ P.natDegree = n ∧
    (∃ alpha : ℂ, ‖alpha‖ = 1 ∧ alpha ^ n = P.coeff 0 / P.coeff n) ∧
    ∀ alpha : ℂ, ‖alpha‖ = 1 → alpha ^ n = P.coeff 0 / P.coeff n →
      (normalizeAt P alpha).coeff 0 = 1 ∧ (normalizeAt P alpha).coeff n = 1 ∧
      (normalizeAt P alpha).natDegree ≤ n ∧ Mirror n (normalizeAt P alpha) ∧
      discImage (normalizeAt P alpha) = (fun w => w / P.coeff 0) '' discImage P ∧
      coefMax n (normalizeAt P alpha) = coefMax n P / ‖P.coeff 0‖ ∧ 1 ≤ coefMax n (normalizeAt P alpha) := by
  have hnorm0 : ‖P.coeff 0‖ = ‖P.coeff n‖ := by simpa using hmir 0 (Nat.zero_le n)
  have han : P.coeff n ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm0; exact h0 (norm_eq_zero.mp hnorm0)
  have hpos : 0 < ‖P.coeff 0‖ := norm_pos_iff.mpr h0
  refine ⟨han, natDegree_eq_of_le_of_coeff_ne_zero hdeg han, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (P.coeff 0 / P.coeff n) (by omega : 0 < n)
    refine ⟨z, ?_, hz⟩
    have h1 : ‖z‖ ^ n = 1 := by
      rw [← norm_pow, hz, norm_div, hnorm0, div_self (norm_pos_iff.mpr han).ne']
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)).mp h1
  · intro alpha ha hpow
    have hc : ∀ k, ‖(normalizeAt P alpha).coeff k‖ = ‖P.coeff k‖ / ‖P.coeff 0‖ :=
      norm_coeff_normalizeAt P ha
    have hQ0 : (normalizeAt P alpha).coeff 0 = 1 := by
      rw [coeff_normalizeAt, pow_zero, mul_one, inv_mul_cancel₀ h0]
    have hQn : (normalizeAt P alpha).coeff n = 1 := by
      rw [coeff_normalizeAt, hpow]; field_simp
    have hQdeg : (normalizeAt P alpha).natDegree ≤ n := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_normalizeAt, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hN)]
      simp
    have hQmir : Mirror n (normalizeAt P alpha) := by
      intro k hk; rw [hc, hc, hmir k hk]
    have hQimg : discImage (normalizeAt P alpha) = (fun w => w / P.coeff 0) '' discImage P := by
      ext w
      simp only [mem_discImage, Set.mem_image, eval_normalizeAt]
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨P.eval (alpha * z), ⟨alpha * z, by rw [norm_mul, ha, one_mul]; exact hz, rfl⟩, ?_⟩
        rw [div_eq_inv_mul]
      · rintro ⟨v, ⟨z, hz, rfl⟩, rfl⟩
        have ha0 : alpha ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
        refine ⟨z / alpha, by rw [norm_div, ha, div_one]; exact hz, ?_⟩
        rw [mul_div_cancel₀ z ha0, div_eq_inv_mul]
    have hQA : coefMax n (normalizeAt P alpha) = coefMax n P / ‖P.coeff 0‖ := by
      apply le_antisymm
      · obtain ⟨k, hk, hkA⟩ := exists_coefMax n (normalizeAt P alpha)
        rw [← hkA, hc]
        exact div_le_div_of_nonneg_right (le_coefMax P hk) hpos.le
      · obtain ⟨k, hk, hkA⟩ := exists_coefMax n P
        rw [← hkA, ← hc]
        exact le_coefMax _ hk
    have hQ1 : 1 ≤ coefMax n (normalizeAt P alpha) := by
      have := le_coefMax (n := n) (normalizeAt P alpha) (Nat.zero_le n)
      rwa [hQ0, norm_one] at this
    exact ⟨hQ0, hQn, hQdeg, hQmir, hQimg, hQA, hQ1⟩

/-- From a disc in `P(𝔻)/a` back to a disc in `P(𝔻)` (P025_body.tex:356-357: "every radius by `1/|a_0|`"). -/
theorem ball_of_ball_div {S : Set ℂ} {a c : ℂ} {r : ℝ} (ha : a ≠ 0)
    (h : Metric.ball c r ⊆ (fun w => w / a) '' S) : Metric.ball (a * c) (r * ‖a‖) ⊆ S := by
  intro w hw
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hwa : w / a ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have he : w / a - c = (w - a * c) / a := by field_simp
    rw [he, norm_div, div_lt_iff₀ hpos]
    exact hw
  obtain ⟨v, hv, hve⟩ := h hwa
  have : v = w := (div_left_inj' ha).mp hve
  exact this ▸ hv

/-- From a disc in `(P - w_0)(𝔻)` to a disc in `P(𝔻)` (P025_body.tex:384: "`P(𝔻) = S(𝔻) + w_*`"). -/
theorem ball_of_ball_sub {P : ℂ[X]} {w0 c : ℂ} {r : ℝ} (h : Metric.ball c r ⊆ discImage (P - C w0)) :
    Metric.ball (c + w0) r ⊆ discImage P := by
  intro w hw
  have hw' : w - w0 ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    rwa [show w - w0 - c = w - (c + w0) by ring]
  obtain ⟨z, hz, hze⟩ := mem_discImage.mp (h hw')
  refine mem_discImage.mpr ⟨z, hz, ?_⟩
  simp only [eval_sub, eval_C] at hze
  linear_combination hze

/-- The choice made in Case 2 when `A > 1`: an index `j` and a disc for the branch where `w_*` is omitted. -/
def SelOK (n : ℕ) (Q : ℂ[X]) : Prop :=
  1 < coefMax n Q → ∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 1 ∧ ‖Q.coeff j‖ = coefMax n Q ∧
    (1 - Q.coeff (n - j) / conj (Q.coeff j) ∉ discImage Q →
      ∃ c : ℂ, Metric.ball c (coefMax n Q) ⊆ discImage Q)

/-- Case 2 for the normalized polynomial (P025_body.tex:359-385), given the choice `SelOK`. -/
theorem normalized_cover (hPSD : HypPSD) {n : ℕ} (hn : 1 ≤ n) {Q : ℂ[X]} (hdeg : Q.natDegree ≤ n)
    (hmir : Mirror n Q) (h0 : Q.coeff 0 = 1) (hn1 : Q.coeff n = 1) (hsel : SelOK n Q) :
    ∃ c : ℂ, Metric.ball c (coefMax n Q) ⊆ discImage Q := by
  have hA1 : 1 ≤ coefMax n Q := by
    have := le_coefMax (n := n) Q (Nat.zero_le n)
    rwa [h0, norm_one] at this
  rcases eq_or_lt_of_le hA1 with hA | hA
  · exact ⟨1, by rw [← hA]; exact case2_A_one hPSD hn hdeg hmir h0 hn1⟩
  · obtain ⟨j, hj1, hjn, hjA, hl⟩ := hsel hA
    by_cases hw : 1 - Q.coeff (n - j) / conj (Q.coeff j) ∈ discImage Q
    · exact ⟨_, rem_4_2_wstar_taken_of hPSD n hn Q hdeg hmir h0 hn1 hA j hj1 hjn hjA hw⟩
    · exact hl hw

/-- Theorem 4.1 from the choice `SelOK` for every normalization of `P` (Cases 1 and 2). -/
theorem cover_of_sel (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hnc : 0 < P.natDegree) (hmir : Mirror n P)
    (hsel : P.coeff 0 ≠ 0 → ∀ alpha : ℂ, ‖alpha‖ = 1 → alpha ^ n = P.coeff 0 / P.coeff n →
      SelOK n (normalizeAt P alpha)) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P := by
  by_cases h0 : P.coeff 0 = 0
  · exact ⟨0, (thm_4_1_case1_of hPSD n hn P hdeg hnc hmir h0).2.2.2.2⟩
  · obtain ⟨-, -, ⟨alpha, ha, hpow⟩, hall⟩ := thm_4_1_normalize_of n hn P hdeg hmir h0
    obtain ⟨hQ0, hQn, hQdeg, hQmir, hQimg, hQA, -⟩ := hall alpha ha hpow
    obtain ⟨c, hc⟩ := normalized_cover hPSD hn hQdeg hQmir hQ0 hQn (hsel h0 alpha ha hpow)
    rw [hQimg, hQA] at hc
    have := ball_of_ball_div h0 hc
    rw [div_mul_cancel₀ _ (norm_pos_iff.mpr h0).ne'] at this
    exact ⟨_, this⟩

/-- The choice for Theorem 4.1: any maximal index, and the circle case (Corollary 3.5) for `S = Q - w_*`. -/
theorem selOK_of_cov (hPSD : HypPSD)
    (hcov : ∀ H : ℂ[X], 1 ≤ H.natDegree → ZerosOnCircle H →
      ∃ c : ℂ, Metric.ball c (coefMaxDeg H) ⊆ discImage H)
    {n : ℕ} (hn : 1 ≤ n) {Q : ℂ[X]} (hdeg : Q.natDegree ≤ n) (hmir : Mirror n Q) (h0 : Q.coeff 0 = 1)
    (hn1 : Q.coeff n = 1) : SelOK n Q := by
  intro hA
  obtain ⟨⟨j, hj1, hjn, hjA⟩, -⟩ := eq_minor_of hPSD n hn Q hdeg hmir h0 hn1 hA
  refine ⟨j, hj1, hjn, hjA, fun hw => ?_⟩
  obtain ⟨hHdeg, -, -, hcirc, hcoef, -⟩ := thm_4_1_wstar_of hPSD n hn Q hdeg hmir h0 hn1 hA j hj1 hjn hjA hw
  obtain ⟨c, hc⟩ := hcov _ (by rw [hHdeg]; exact hn) hcirc
  rw [hcoef] at hc
  exact ⟨_, ball_of_ball_sub hc⟩

/-- Row `thm_4_1` (P025_body.tex:334-339), from `hPSD` and the circle case `hcov` (Corollary 3.5). -/
theorem thm_4_1_of (hPSD : HypPSD)
    (hcov : ∀ H : ℂ[X], 1 ≤ H.natDegree → ZerosOnCircle H →
      ∃ c : ℂ, Metric.ball c (coefMaxDeg H) ⊆ discImage H)
    (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree)
    (hmir : Mirror n P) : ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P := by
  refine cover_of_sel hPSD n hn P hdeg hnc hmir (fun h0 alpha ha hpow => ?_)
  obtain ⟨hQ0, hQn, hQdeg, hQmir, -, -, -⟩ := (thm_4_1_normalize_of n hn P hdeg hmir h0).2.2.2 alpha ha hpow
  exact selOK_of_cov hPSD hcov hn hQdeg hQmir hQ0 hQn

/-- Row `rem_4_2_no_coef` (P025_body.tex:388-390): no circle-case input when `a_0 = 0` or `A ≤ 2|a_0|`. -/
theorem rem_4_2_no_coef_of (hPSD : HypPSD) (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n)
    (hnc : 0 < P.natDegree) (hmir : Mirror n P) (hsmall : P.coeff 0 = 0 ∨ coefMax n P ≤ 2 * ‖P.coeff 0‖) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P := by
  refine cover_of_sel hPSD n hn P hdeg hnc hmir (fun h0 alpha ha hpow => ?_)
  obtain ⟨hQ0, hQn, hQdeg, hQmir, -, hQA, -⟩ := (thm_4_1_normalize_of n hn P hdeg hmir h0).2.2.2 alpha ha hpow
  have hsm : coefMax n P ≤ 2 * ‖P.coeff 0‖ := hsmall.resolve_left h0
  have hpos : 0 < ‖P.coeff 0‖ := norm_pos_iff.mpr h0
  have hQ2 : coefMax n (normalizeAt P alpha) ≤ 2 := by
    rw [hQA, div_le_iff₀ hpos]; linarith
  intro hA
  obtain ⟨⟨j, hj1, hjn, hjA⟩, hall⟩ := eq_minor_of hPSD n hn _ hQdeg hQmir hQ0 hQn hA
  obtain ⟨hE1, -⟩ := hall j hj1 hjn hjA
  refine ⟨j, hj1, hjn, hjA, fun _ => ⟨1 + (normalizeAt P alpha).coeff (n - j) /
    conj ((normalizeAt P alpha).coeff j), fun w hwb => ?_⟩⟩
  refine eq_punctured_of hPSD n hn _ hQdeg hQmir hQ0 hQn hA j hj1 hjn hjA ⟨hwb, ?_⟩
  rintro rfl
  have h2 := ((rem_4_2_dist_of _ hE1 (coefMax n (normalizeAt P alpha))).2).mp hwb
  linarith

end Sheil
