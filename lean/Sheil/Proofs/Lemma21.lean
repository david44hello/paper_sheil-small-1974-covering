/- Sheil/Proofs/Lemma21.lean — proofs of the rows lem_2_1_a, lem_2_1_b, lem_2_1_mirror, lem_2_1_circle of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Defs.Basic
import Sheil.Proofs.Basic

namespace Sheil

open Polynomial ComplexConjugate

/-! ### Roots of the reversal and of `P*` -/

/-- The reversal of `X - C a` (`a ≠ 0`) is `C (-a) * (X - C a⁻¹)`, so its only root is `a⁻¹`. -/
theorem roots_reverse_X_sub_C (a : ℂ) (ha : a ≠ 0) : (X - C a : ℂ[X]).reverse.roots = {a⁻¹} := by
  have h1 : (X - C a : ℂ[X]).reverse = C (-a) * (X - C a⁻¹) := by
    unfold reverse
    rw [natDegree_X_sub_C, reflect_sub, reflect_one_X, reflect_C, mul_sub, ← C_mul, neg_mul,
      mul_inv_cancel₀ ha, C_neg, C_neg, C_1, pow_one]
    ring
  rw [h1, roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C]

/-- The reversal of `∏_{a ∈ s} (X - C a)` has roots `s.map (·⁻¹)` when `0 ∉ s`. -/
theorem roots_reverse_prod (s : Multiset ℂ) (hs : (0 : ℂ) ∉ s) :
    ((s.map fun a => X - C a).prod).reverse.roots = s.map fun ζ => ζ⁻¹ := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, Multiset.map_zero, ← C_1, reverse_C, roots_C]
  | cons a s ih =>
    have ha : a ≠ 0 := fun h => hs (h ▸ Multiset.mem_cons_self a s)
    have hs' : (0 : ℂ) ∉ s := fun h => hs (Multiset.mem_cons_of_mem h)
    have hne : (X - C a : ℂ[X]).reverse * ((s.map fun a => X - C a).prod).reverse ≠ 0 :=
      mul_ne_zero (reverse_eq_zero.not.mpr (X_sub_C_ne_zero a))
        (reverse_eq_zero.not.mpr (monic_multisetProd_X_sub_C s).ne_zero)
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, roots_mul hne,
      roots_reverse_X_sub_C a ha, ih hs', Multiset.map_cons, Multiset.singleton_add]

/-- Over ℂ, if `P(0) ≠ 0` then the roots of the reversal `z^{deg P} P(1/z)` are the `ζ⁻¹`, `ζ` a root of `P`. -/
theorem roots_reverse_of_coeff_zero (P : ℂ[X]) (h0 : P.coeff 0 ≠ 0) :
    P.reverse.roots = P.roots.map fun ζ => ζ⁻¹ := by
  have hP0 : P ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have hnot : (0 : ℂ) ∉ P.roots := by
    rw [mem_roots hP0, IsRoot.def, ← coeff_zero_eq_eval_zero]
    exact h0
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := P))
  calc P.reverse.roots
      = (C P.leadingCoeff * (P.roots.map fun a => X - C a).prod).reverse.roots := by rw [hfac]
    _ = P.roots.map fun ζ => ζ⁻¹ := by
      rw [reverse_mul_of_domain, reverse_C, roots_C_mul _ hlc, roots_reverse_prod _ hnot]

/-- Over ℂ, if `P(0) ≠ 0` then the roots of `P*` (with `n = deg P`) are the `(conj ζ)⁻¹`, `ζ` a root of `P`. -/
theorem roots_pstar (P : ℂ[X]) (h0 : P.coeff 0 ≠ 0) :
    (pstar P.natDegree P).roots = P.roots.map fun ζ => (conj ζ)⁻¹ := by
  rw [pstar_eq_reflect_map _ _ le_rfl]
  change (P.reverse.map (starRingEnd ℂ)).roots = _
  rw [← roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
      IsAlgClosed.card_roots_eq_natDegree, roots_reverse_of_coeff_zero P h0, Multiset.map_map]
  refine Multiset.map_congr rfl fun ζ _ => ?_
  simp [map_inv₀]

/-! ### Same roots, proportional; symmetric zeros as invariant root multisets -/

/-- Over ℂ, two polynomials with the same roots (with multiplicity) are proportional. -/
theorem eq_C_mul_of_roots_eq (P Q : ℂ[X]) (hP : P ≠ 0) (h : Q.roots = P.roots) :
    Q = C (Q.leadingCoeff / P.leadingCoeff) * P := by
  have hQf := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := Q))
  have hPf := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := P))
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  calc Q = C Q.leadingCoeff * (Q.roots.map fun a => X - C a).prod := hQf.symm
    _ = C (Q.leadingCoeff / P.leadingCoeff) * (C P.leadingCoeff * (P.roots.map fun a => X - C a).prod) := by
        rw [h, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hlc]
    _ = C (Q.leadingCoeff / P.leadingCoeff) * P := by rw [hPf]

/-- For an involution `g`, a multiset is `g`-invariant iff `count ζ = count (g ζ)` for every `ζ`. -/
theorem map_eq_self_iff_count {g : ℂ → ℂ} (hg : Function.Involutive g) (s : Multiset ℂ) :
    s.map g = s ↔ ∀ ζ, s.count ζ = s.count (g ζ) := by
  have key : ∀ ζ, (s.map g).count ζ = s.count (g ζ) := by
    intro ζ
    have := Multiset.count_map_eq_count' g s hg.injective (g ζ)
    rwa [hg ζ] at this
  constructor
  · intro h ζ
    rw [← key ζ, h]
  · intro h
    ext ζ
    rw [key ζ, h ζ]

theorem conjInv_involutive : Function.Involutive fun ζ : ℂ => (conj ζ)⁻¹ := by
  intro ζ
  simp [map_inv₀]

theorem zerosSymmConjInv_iff (P : ℂ[X]) :
    ZerosSymmConjInv P ↔ (P.roots.map fun ζ => (conj ζ)⁻¹) = P.roots := by
  rw [map_eq_self_iff_count conjInv_involutive]
  simp only [ZerosSymmConjInv, count_roots]

theorem zerosSymmInv_iff (P : ℂ[X]) :
    ZerosSymmInv P ↔ (P.roots.map fun ζ => ζ⁻¹) = P.roots := by
  rw [map_eq_self_iff_count inv_involutive]
  simp only [ZerosSymmInv, count_roots]

/-! ### Coefficient facts -/

/-- From `conj a_{n-k} = λ a_k` at `k = 0` and `k = n`, with `a_0 ≠ 0`: `|λ| = 1`. -/
theorem norm_eq_one_of_coeff_conj (n : ℕ) (P : ℂ[X]) (h0 : P.coeff 0 ≠ 0) (lam : ℂ)
    (h : ∀ k ≤ n, conj (P.coeff (n - k)) = lam * P.coeff k) : ‖lam‖ = 1 := by
  have e0 := congrArg norm (h 0 (Nat.zero_le n))
  have en := congrArg norm (h n le_rfl)
  simp only [Nat.sub_zero, Nat.sub_self, Complex.norm_conj, norm_mul] at e0 en
  have h1 : (‖lam‖ * ‖lam‖ - 1) * ‖P.coeff 0‖ = 0 := by
    rw [e0] at en
    linear_combination -en
  rcases mul_eq_zero.mp h1 with h2 | h2
  · nlinarith [norm_nonneg lam]
  · exact absurd (norm_eq_zero.mp h2) h0

/-- On the unit circle `(conj ζ)⁻¹ = ζ`. -/
theorem conj_inv_eq_self_of_norm {ζ : ℂ} (hζ : ‖ζ‖ = 1) : (conj ζ)⁻¹ = ζ := by
  apply inv_eq_of_mul_eq_one_right
  rw [Complex.conj_mul', hζ]
  norm_num

/-! ### Lemma 2.1 -/

theorem lem_2_1_a_proved (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree = n) (h0 : P.eval 0 ≠ 0) :
    (ZerosSymmConjInv P ↔ ∃ lam : ℂ, ‖lam‖ = 1 ∧ pstar n P = C lam * P) ∧
    ∀ lam : ℂ, pstar n P = C lam * P → ∀ k ≤ n, conj (P.coeff (n - k)) = lam * P.coeff k := by
  have hc : ∀ lam : ℂ, pstar n P = C lam * P → ∀ k ≤ n, conj (P.coeff (n - k)) = lam * P.coeff k := by
    intro lam h k hk
    have := congrArg (Polynomial.coeff · k) h
    simpa only [coeff_pstar, hk, ↓reduceIte, coeff_C_mul] using this
  refine ⟨?_, hc⟩
  have h0' : P.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  have hP : P ≠ 0 := fun h => h0' (by rw [h, coeff_zero])
  subst hdeg
  rw [zerosSymmConjInv_iff, ← roots_pstar P h0']
  constructor
  · intro hr
    have hp := eq_C_mul_of_roots_eq P _ hP hr
    exact ⟨_, norm_eq_one_of_coeff_conj _ P h0' _ (hc _ hp), hp⟩
  · rintro ⟨lam, hlam, h⟩
    have hl0 : lam ≠ 0 := by
      rintro rfl
      simp at hlam
    rw [h, roots_C_mul _ hl0]

theorem lem_2_1_b_proved (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree = n) (h0 : P.eval 0 ≠ 0) :
    ZerosSymmInv P ↔ PlusMinusPalindromic n P := by
  have h0' : P.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  have hP : P ≠ 0 := fun h => h0' (by rw [h, coeff_zero])
  subst hdeg
  rw [zerosSymmInv_iff, ← roots_reverse_of_coeff_zero P h0']
  constructor
  · intro hr
    obtain ⟨c, hrev⟩ : ∃ c : ℂ, P.reverse = C c * P := ⟨_, eq_C_mul_of_roots_eq P _ hP hr⟩
    have hcoef : ∀ k ≤ P.natDegree, P.coeff (P.natDegree - k) = c * P.coeff k := by
      intro k hk
      have := congrArg (Polynomial.coeff · k) hrev
      simpa only [coeff_reverse, revAt_le hk, coeff_C_mul] using this
    refine ⟨c, ?_, hcoef⟩
    have e0 := hcoef 0 (Nat.zero_le _)
    have en := hcoef _ le_rfl
    simp only [Nat.sub_zero, Nat.sub_self] at e0 en
    have h1 : (c * c - 1) * P.coeff 0 = 0 := by linear_combination -en - c * e0
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact mul_self_eq_one_iff.mp (sub_eq_zero.mp h2)
    · exact absurd h2 h0'
  · rintro ⟨eps, heps, hcoef⟩
    have hrev : P.reverse = C eps * P := by
      ext k
      rw [coeff_reverse, coeff_C_mul]
      by_cases hk : k ≤ P.natDegree
      · rw [revAt_le hk, hcoef k hk]
      · have hk' : P.natDegree < k := Nat.lt_of_not_le hk
        rw [revAt_eq_self_of_lt hk', coeff_eq_zero_of_natDegree_lt hk', mul_zero]
    have he0 : eps ≠ 0 := by
      rcases heps with rfl | rfl <;> norm_num
    rw [hrev, roots_C_mul _ he0]

theorem lem_2_1_mirror_proved (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree = n) (h0 : P.eval 0 ≠ 0)
    (hsym : ZerosSymmConjInv P ∨ ZerosSymmInv P) : Mirror n P := by
  intro k hk
  rcases hsym with h | h
  · obtain ⟨lam, hlam, hp⟩ := (lem_2_1_a_proved n P hdeg h0).1.mp h
    have := congrArg norm ((lem_2_1_a_proved n P hdeg h0).2 lam hp k hk)
    rw [Complex.norm_conj, norm_mul, hlam, one_mul] at this
    exact this.symm
  · obtain ⟨eps, heps, hc⟩ := (lem_2_1_b_proved n P hdeg h0).mp h
    have := congrArg norm (hc k hk)
    have hn : ‖eps‖ = 1 := by
      rcases heps with rfl | rfl <;> simp
    rw [norm_mul, hn, one_mul] at this
    exact this.symm

theorem lem_2_1_circle_proved (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) : SelfInversive P := by
  have h0 : P.eval 0 ≠ 0 := by
    intro h
    have := hz 0 h
    simp at this
  refine ⟨hdeg, (lem_2_1_a_proved P.natDegree P rfl h0).1.mp ?_⟩
  intro ζ
  by_cases hζ : ‖ζ‖ = 1
  · rw [conj_inv_eq_self_of_norm hζ]
  · have h1 : ¬ P.IsRoot ζ := fun h => hζ (hz ζ h)
    have h2 : ¬ P.IsRoot (conj ζ)⁻¹ := by
      intro h
      apply hζ
      have := hz _ h
      rwa [norm_inv, Complex.norm_conj, inv_eq_one] at this
    rw [rootMultiplicity_eq_zero h1, rootMultiplicity_eq_zero h2]

end Sheil
