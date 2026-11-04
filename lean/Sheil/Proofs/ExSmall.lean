/- Sheil/Proofs/ExSmall.lean — proofs of the rows intro_ex_three_i, intro_ex_four, fig1_regions, ex_5_1 of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Defs.Examples
import Sheil.Proofs.Sec4

namespace Sheil

open Polynomial ComplexConjugate

/-! ### Degree-two tools -/

/-- `P* = λP` for `deg P ≤ 2` from the three coefficient equations. -/
theorem exs_pstar_two {P : ℂ[X]} (lam : ℂ) (hdeg : P.natDegree ≤ 2)
    (h0 : conj (P.coeff 2) = lam * P.coeff 0) (h1 : conj (P.coeff 1) = lam * P.coeff 1)
    (h2 : conj (P.coeff 0) = lam * P.coeff 2) : pstar 2 P = C lam * P := by
  ext k
  rw [coeff_pstar, coeff_C_mul]
  by_cases hk : k ≤ 2
  · rw [if_pos hk]
    interval_cases k
    · exact h0
    · exact h1
    · exact h2
  · rw [if_neg hk, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k), mul_zero]

/-- The coefficient equation of `P* = λP`. -/
theorem exs_coeff_of_pstar {n : ℕ} {P : ℂ[X]} {lam : ℂ} (h : pstar n P = C lam * P) {k : ℕ} (hk : k ≤ n) :
    conj (P.coeff (n - k)) = lam * P.coeff k := by
  have := congrArg (fun Q => Q.coeff k) h
  simpa only [coeff_pstar, hk, ite_true, coeff_C_mul] using this

/-- `coefMax 2 P` is the largest of the three coefficient moduli. -/
theorem exs_coefMax_two (P : ℂ[X]) {A : ℝ} (h0 : ‖P.coeff 0‖ ≤ A) (h1 : ‖P.coeff 1‖ ≤ A) (h2 : ‖P.coeff 2‖ ≤ A)
    (hA : ‖P.coeff 0‖ = A ∨ ‖P.coeff 1‖ = A ∨ ‖P.coeff 2‖ = A) : coefMax 2 P = A := by
  apply le_antisymm
  · unfold coefMax
    refine Finset.sup'_le _ _ (fun k hk => ?_)
    have hk3 : k < 3 := Finset.mem_range.mp hk
    interval_cases k
    · exact h0
    · exact h1
    · exact h2
  · rcases hA with h | h | h <;> rw [← h] <;> exact le_coefMax P (by norm_num)

/-! ### `1 + 3iz + z^2` (P025_body.tex:106-108) -/

theorem exs_threeI_coeff0 : polyThreeI.coeff 0 = 1 := by simp [polyThreeI, coeff_one, coeff_X, coeff_X_pow]
theorem exs_threeI_coeff1 : polyThreeI.coeff 1 = 3 * Complex.I := by
  simp [polyThreeI, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_threeI_coeff2 : polyThreeI.coeff 2 = 1 := by
  simp [polyThreeI, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]

theorem exs_threeI_natDegree : polyThreeI.natDegree = 2 := by
  unfold polyThreeI
  compute_degree!

theorem exs_threeI_pm : PlusMinusPalindromic 2 polyThreeI := by
  refine ⟨1, Or.inl rfl, fun k hk => ?_⟩
  interval_cases k <;> simp [exs_threeI_coeff0, exs_threeI_coeff1, exs_threeI_coeff2]

theorem exs_threeI_not_si : ¬ SelfInversive polyThreeI := by
  rintro ⟨-, lam, -, h⟩
  rw [exs_threeI_natDegree] at h
  have e0 := exs_coeff_of_pstar h (k := 0) (by norm_num)
  have e1 := exs_coeff_of_pstar h (k := 1) (by norm_num)
  simp only [Nat.sub_zero, Nat.reduceSub, exs_threeI_coeff0, exs_threeI_coeff1, exs_threeI_coeff2, map_one,
    mul_one] at e0 e1
  rw [← e0] at e1
  simp [map_mul, Complex.conj_I] at e1
  have := congrArg Complex.im e1
  simp at this
  norm_num at this

/-- Row `intro_ex_three_i`. -/
theorem intro_ex_three_i_proved :
    polyThreeI.natDegree = 2 ∧ PlusMinusPalindromic 2 polyThreeI ∧ ¬ SelfInversive polyThreeI :=
  ⟨exs_threeI_natDegree, exs_threeI_pm, exs_threeI_not_si⟩

/-! ### `1 + 4z + z^2` (P025_body.tex:129-131) -/

theorem exs_four_coeff0 : polyFour.coeff 0 = 1 := by simp [polyFour, coeff_one, coeff_X, coeff_X_pow]
theorem exs_four_coeff1 : polyFour.coeff 1 = 4 := by simp [polyFour, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_four_coeff2 : polyFour.coeff 2 = 1 := by simp [polyFour, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]

theorem exs_four_natDegree : polyFour.natDegree = 2 := by
  unfold polyFour
  compute_degree!

theorem exs_four_si : SelfInversive polyFour := by
  refine ⟨by rw [exs_four_natDegree]; norm_num, 1, norm_one, ?_⟩
  rw [exs_four_natDegree]
  apply exs_pstar_two 1 exs_four_natDegree.le <;>
    simp [exs_four_coeff0, exs_four_coeff1, exs_four_coeff2, Complex.conj_ofNat]

theorem exs_four_pm : PlusMinusPalindromic 2 polyFour := by
  refine ⟨1, Or.inl rfl, fun k hk => ?_⟩
  interval_cases k <;> simp [exs_four_coeff0, exs_four_coeff1, exs_four_coeff2]

theorem exs_four_eval (z : ℂ) : polyFour.eval z = 1 + 4 * z + z ^ 2 := by simp [polyFour]

theorem exs_four_maxMod : maxMod polyFour = 6 := by
  unfold maxMod
  apply IsGreatest.csSup_eq
  refine ⟨⟨1, by simp, by simp only [exs_four_eval]; norm_num⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz1 : ‖z‖ = 1 := by simpa using hz
  show ‖polyFour.eval z‖ ≤ 6
  rw [exs_four_eval]
  calc ‖1 + 4 * z + z ^ 2‖ ≤ ‖1 + 4 * z‖ + ‖z ^ 2‖ := norm_add_le _ _
    _ ≤ ‖(1 : ℂ)‖ + ‖4 * z‖ + ‖z ^ 2‖ := by gcongr; exact norm_add_le _ _
    _ = 6 := by rw [norm_mul, norm_pow, hz1]; norm_num

theorem exs_four_coefMaxDeg : coefMaxDeg polyFour = 4 := by
  unfold coefMaxDeg
  rw [exs_four_natDegree]
  apply exs_coefMax_two <;> simp [exs_four_coeff0, exs_four_coeff1, exs_four_coeff2]

/-- Row `intro_ex_four`. -/
theorem intro_ex_four_proved :
    SelfInversive polyFour ∧ maxMod polyFour / 2 = 3 ∧ coefMaxDeg polyFour = 4 :=
  ⟨exs_four_si, by rw [exs_four_maxMod]; norm_num, exs_four_coefMaxDeg⟩

/-- `1 + 4z + z^2` has the zero `-2 + √3` off the circle. -/
theorem exs_four_not_circle : ¬ ZerosOnCircle polyFour := by
  intro h
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2 : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hroot : polyFour.IsRoot ((-2 + Real.sqrt 3 : ℝ) : ℂ) := by
    rw [IsRoot, exs_four_eval]
    have hc : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by rw [← Complex.ofReal_pow, hs]; norm_num
    push_cast
    linear_combination hc
  have := h _ hroot
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)] at this
  linarith

/-! ### The other Figure 1 witnesses -/

theorem exs_sq_coeff0 : polyOnePlusSq.coeff 0 = 1 := by simp [polyOnePlusSq, coeff_one, coeff_X_pow]
theorem exs_sq_coeff1 : polyOnePlusSq.coeff 1 = 0 := by simp [polyOnePlusSq, coeff_one, coeff_X_pow]
theorem exs_sq_coeff2 : polyOnePlusSq.coeff 2 = 1 := by simp [polyOnePlusSq, coeff_one, coeff_X_pow]
theorem exs_sq_natDegree : polyOnePlusSq.natDegree = 2 := by
  unfold polyOnePlusSq
  compute_degree!

theorem exs_sq_facts :
    SelfInversive polyOnePlusSq ∧ PlusMinusPalindromic 2 polyOnePlusSq ∧ ZerosOnCircle polyOnePlusSq := by
  refine ⟨⟨by rw [exs_sq_natDegree]; norm_num, 1, norm_one, ?_⟩, ⟨1, Or.inl rfl, fun k hk => ?_⟩, fun z hz => ?_⟩
  · rw [exs_sq_natDegree]
    apply exs_pstar_two 1 exs_sq_natDegree.le <;> simp [exs_sq_coeff0, exs_sq_coeff1, exs_sq_coeff2]
  · interval_cases k <;> simp [exs_sq_coeff0, exs_sq_coeff1, exs_sq_coeff2]
  · have h2 : z ^ 2 = -1 := by
      have := hz
      simp [IsRoot, polyOnePlusSq] at this
      linear_combination this
    have h3 := congrArg norm h2
    rw [norm_pow, norm_neg, norm_one] at h3
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [h3]

theorem exs_xsubi_facts :
    polyXSubI.natDegree = 1 ∧ ZerosOnCircle polyXSubI ∧ ¬ PlusMinusPalindromic 1 polyXSubI := by
  refine ⟨by unfold polyXSubI; compute_degree!, fun z hz => ?_, ?_⟩
  · have : z = Complex.I := by
      simpa [IsRoot, polyXSubI, sub_eq_zero] using hz
    rw [this, Complex.norm_I]
  · rintro ⟨eps, heps, h⟩
    have h0 := h 0 (by norm_num)
    simp [polyXSubI, coeff_X, coeff_C] at h0
    rcases heps with rfl | rfl
    · have := congrArg Complex.im h0
      simp at this
    · have := congrArg Complex.im h0
      simp at this

theorem exs_sio_coeff0 : polySelfInvOnly.coeff 0 = -1 := by
  simp [polySelfInvOnly, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_sio_coeff1 : polySelfInvOnly.coeff 1 = -(5 / 2 * Complex.I) := by
  simp [polySelfInvOnly, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_sio_coeff2 : polySelfInvOnly.coeff 2 = 1 := by
  simp [polySelfInvOnly, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_sio_natDegree : polySelfInvOnly.natDegree = 2 := by
  unfold polySelfInvOnly
  compute_degree!

theorem exs_sio_facts :
    SelfInversive polySelfInvOnly ∧ ¬ PlusMinusPalindromic 2 polySelfInvOnly ∧ ¬ ZerosOnCircle polySelfInvOnly := by
  refine ⟨⟨by rw [exs_sio_natDegree]; norm_num, -1, by simp, ?_⟩, ?_, fun h => ?_⟩
  · rw [exs_sio_natDegree]
    apply exs_pstar_two (-1) exs_sio_natDegree.le <;>
      simp [exs_sio_coeff0, exs_sio_coeff1, exs_sio_coeff2, map_neg, map_mul, map_div₀, map_ofNat, Complex.conj_I]
  · rintro ⟨eps, heps, hp⟩
    have h0 := hp 0 (by norm_num)
    have h1 := hp 1 (by norm_num)
    simp only [Nat.sub_zero, Nat.reduceSub, exs_sio_coeff0, exs_sio_coeff1, exs_sio_coeff2] at h0 h1
    rcases heps with rfl | rfl
    · norm_num at h0
    · have := congrArg Complex.im h1
      simp at this
      linarith
  · have hroot : polySelfInvOnly.IsRoot (2 * Complex.I) := by
      simp only [IsRoot, polySelfInvOnly, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one]
      ring_nf
      rw [Complex.I_sq]
      ring
    have := h _ hroot
    rw [norm_mul, Complex.norm_I] at this
    norm_num at this

theorem exs_mo_coeff0 : polyMirrorOnly.coeff 0 = 1 := by
  simp [polyMirrorOnly, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_mo_coeff1 : polyMirrorOnly.coeff 1 = 1 := by
  simp [polyMirrorOnly, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_mo_coeff2 : polyMirrorOnly.coeff 2 = Complex.I := by
  simp [polyMirrorOnly, coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
theorem exs_mo_natDegree : polyMirrorOnly.natDegree = 2 := by
  unfold polyMirrorOnly
  compute_degree!

theorem exs_mo_facts :
    polyMirrorOnly.natDegree = 2 ∧ Mirror 2 polyMirrorOnly ∧ ¬ SelfInversive polyMirrorOnly ∧
      ¬ PlusMinusPalindromic 2 polyMirrorOnly := by
  refine ⟨exs_mo_natDegree, fun k hk => ?_, ?_, ?_⟩
  · interval_cases k <;> simp [exs_mo_coeff0, exs_mo_coeff1, exs_mo_coeff2]
  · rintro ⟨-, lam, -, h⟩
    rw [exs_mo_natDegree] at h
    have e0 := exs_coeff_of_pstar h (k := 0) (by norm_num)
    have e1 := exs_coeff_of_pstar h (k := 1) (by norm_num)
    simp only [Nat.sub_zero, Nat.reduceSub, exs_mo_coeff0, exs_mo_coeff1, exs_mo_coeff2, map_one, mul_one,
      Complex.conj_I] at e0 e1
    rw [← e1] at e0
    have := congrArg Complex.im e0
    simp at this
  · rintro ⟨eps, heps, hp⟩
    have h0 := hp 0 (by norm_num)
    simp only [Nat.sub_zero, exs_mo_coeff0, exs_mo_coeff2, mul_one] at h0
    rcases heps with rfl | rfl
    · have := congrArg Complex.im h0
      simp at this
    · have := congrArg Complex.im h0
      simp at this

/-- Row `fig1_regions`. -/
theorem fig1_regions_proved :
    (SelfInversive polyOnePlusSq ∧ PlusMinusPalindromic 2 polyOnePlusSq ∧ ZerosOnCircle polyOnePlusSq) ∧
    (polyXSubI.natDegree = 1 ∧ ZerosOnCircle polyXSubI ∧ ¬ PlusMinusPalindromic 1 polyXSubI) ∧
    (SelfInversive polyFour ∧ PlusMinusPalindromic 2 polyFour ∧ ¬ ZerosOnCircle polyFour) ∧
    (SelfInversive polySelfInvOnly ∧ ¬ PlusMinusPalindromic 2 polySelfInvOnly ∧ ¬ ZerosOnCircle polySelfInvOnly) ∧
    (PlusMinusPalindromic 2 polyThreeI ∧ ¬ SelfInversive polyThreeI) ∧
    (polyMirrorOnly.natDegree = 2 ∧ Mirror 2 polyMirrorOnly ∧ ¬ SelfInversive polyMirrorOnly ∧
      ¬ PlusMinusPalindromic 2 polyMirrorOnly) :=
  ⟨exs_sq_facts, exs_xsubi_facts, ⟨exs_four_si, exs_four_pm, exs_four_not_circle⟩, exs_sio_facts,
    ⟨exs_threeI_pm, exs_threeI_not_si⟩, exs_mo_facts⟩

/-! ### Example 5.1: `1 + z^n` (P025_body.tex:433-436) -/

theorem exs_pow_coeff (n k : ℕ) :
    (polyOnePlusPow n).coeff k = (if k = 0 then 1 else 0) + (if k = n then 1 else 0) := by
  simp [polyOnePlusPow, coeff_one, coeff_X_pow, eq_comm]

theorem exs_pow_natDegree {n : ℕ} (hn : 1 ≤ n) : (polyOnePlusPow n).natDegree = n := by
  unfold polyOnePlusPow
  rw [natDegree_add_eq_right_of_natDegree_lt (by rw [natDegree_one, natDegree_X_pow]; omega), natDegree_X_pow]

theorem exs_pow_image {n : ℕ} (hn : 1 ≤ n) : discImage (polyOnePlusPow n) = Metric.ball 1 1 := by
  ext w
  rw [mem_discImage, Metric.mem_ball, dist_eq_norm]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [polyOnePlusPow, eval_add, eval_one, eval_pow, eval_X, add_sub_cancel_left, norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz (by omega)
  · intro hw
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w - 1) (by omega : 0 < n)
    refine ⟨z, ?_, ?_⟩
    · by_contra hge
      push Not at hge
      have : 1 ≤ ‖z‖ ^ n := one_le_pow₀ hge
      rw [← norm_pow, hz] at this
      linarith
    · simp [polyOnePlusPow, hz]

/-- In `D(1,1)`, the points `c + 1` and `c - 1` cannot both lie. -/
theorem exs_not_both {c : ℂ} (h1 : c + 1 ∈ Metric.ball (1 : ℂ) 1) (h2 : c - 1 ∈ Metric.ball (1 : ℂ) 1) : False := by
  rw [Metric.mem_ball, dist_eq_norm] at h1 h2
  have : ‖(c + 1 - 1) - (c - 1 - 1)‖ ≤ ‖c + 1 - 1‖ + ‖c - 1 - 1‖ := norm_sub_le _ _
  rw [show (c + 1 - 1) - (c - 1 - 1) = (2 : ℂ) by ring] at this
  norm_num at this
  have e1 : ‖c‖ < 1 := by simpa using h1
  linarith

/-- Row `ex_5_1`. -/
theorem ex_5_1_proved (n : ℕ) (hn : 1 ≤ n) :
    Mirror n (polyOnePlusPow n) ∧ (polyOnePlusPow n).natDegree = n ∧ coefMaxDeg (polyOnePlusPow n) = 1 ∧
    discImage (polyOnePlusPow n) = Metric.ball 1 1 ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage (polyOnePlusPow n) → r ≤ 1) ∧
    (∀ c : ℂ, ¬ Metric.closedBall c 1 ⊆ discImage (polyOnePlusPow n)) := by
  have hn0 : n ≠ 0 := by omega
  have hn0' : 0 ≠ n := Ne.symm hn0
  refine ⟨fun k hk => ?_, exs_pow_natDegree hn, ?_, exs_pow_image hn, fun c r h => ?_, fun c h => ?_⟩
  · rw [exs_pow_coeff, exs_pow_coeff]
    by_cases h0 : k = 0
    · subst h0; simp [hn0, hn0']
    · by_cases hkn : k = n
      · subst hkn; simp [h0, hn0']
      · have h1 : n - k ≠ 0 := by omega
        have h2 : n - k ≠ n := by omega
        simp [h0, hkn, h1, h2]
  · unfold coefMaxDeg
    rw [exs_pow_natDegree hn]
    apply le_antisymm
    · unfold coefMax
      refine Finset.sup'_le _ _ (fun k _ => ?_)
      rw [exs_pow_coeff]
      by_cases h0 : k = 0
      · subst h0; simp [hn0']
      · by_cases hkn : k = n <;> simp [h0, hkn, hn0]
    · have := le_coefMax (n := n) (k := 0) (polyOnePlusPow n) (Nat.zero_le n)
      rw [exs_pow_coeff] at this
      simpa [hn0'] using this
  · rw [exs_pow_image hn] at h
    by_contra hr
    push Not at hr
    refine exs_not_both (c := c) (h (a := c + 1) ?_) (h (a := c - 1) ?_) <;>
      rw [Metric.mem_ball, dist_eq_norm] <;> simpa using hr
  · rw [exs_pow_image hn] at h
    refine exs_not_both (c := c) (h (a := c + 1) ?_) (h (a := c - 1) ?_) <;>
      rw [Metric.mem_closedBall, dist_eq_norm] <;> simp

#print axioms intro_ex_three_i_proved
#print axioms intro_ex_four_proved
#print axioms fig1_regions_proved
#print axioms ex_5_1_proved

end Sheil
