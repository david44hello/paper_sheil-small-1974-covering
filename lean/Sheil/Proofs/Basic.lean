/- Sheil/Proofs/Basic.lean — lemmas used by the proofs.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Defs.Basic

namespace Sheil

open Polynomial ComplexConjugate
open scoped ComplexOrder

/-- The `2 × 2` principal minor of a positive semidefinite complex matrix: `|K_ij|^2 ≤ K_ii K_jj`. -/
theorem psd_minor {n : ℕ} {K : Matrix (Fin n) (Fin n) ℂ} (hK : K.PosSemidef) (i j : Fin n) :
    ‖K i j‖ ^ 2 ≤ (K i i).re * (K j j).re := by
  have hsub := hK.submatrix ![i, j]
  have hdet := hsub.det_nonneg
  have hherm : K j i = conj (K i j) := by
    have := congrFun (congrFun hK.1 j) i
    simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
    exact this.symm
  have hii : (K i i).im = 0 := by
    have := congrFun (congrFun hK.1 i) i
    simp [Matrix.conjTranspose_apply] at this
    exact Complex.conj_eq_iff_im.mp this
  have hjj : (K j j).im = 0 := by
    have := congrFun (congrFun hK.1 j) j
    simp [Matrix.conjTranspose_apply] at this
    exact Complex.conj_eq_iff_im.mp this
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    hherm] at hdet
  have hre := (Complex.nonneg_iff.mp hdet).1
  simp only [Complex.sub_re, Complex.mul_re, hii, hjj, mul_zero, sub_zero, Complex.conj_re,
    Complex.conj_im] at hre
  have hn : ‖K i j‖ ^ 2 = (K i j).re * (K i j).re + (K i j).im * (K i j).im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [hn]

/-- The coefficients of `P*` (P025_body.tex:43, 163). -/
theorem coeff_pstar (n : ℕ) (H : ℂ[X]) (k : ℕ) :
    (pstar n H).coeff k = if k ≤ n then conj (H.coeff (n - k)) else 0 := by
  unfold pstar
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- For `deg H ≤ n`, `P*` is the conjugate of the `n`-reflection of `H`. -/
theorem pstar_eq_reflect_map (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) :
    pstar n H = (H.reflect n).map (starRingEnd ℂ) := by
  ext k
  rw [coeff_pstar, coeff_map, coeff_reflect]
  by_cases hk : k ≤ n
  · simp [hk, revAt_le hk]
  · have hk' : n < k := Nat.lt_of_not_le hk
    rw [revAt_eq_self_of_lt hk', coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk')]
    simp [hk]

/-- `P*` of a product: `(FG)* = F* G*` (degrees at most `m` and `l`). -/
theorem pstar_mul (m l : ℕ) (F G : ℂ[X]) (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ l) :
    pstar (m + l) (F * G) = pstar m F * pstar l G := by
  rw [pstar_eq_reflect_map _ _ (le_trans natDegree_mul_le (Nat.add_le_add hF hG)),
    pstar_eq_reflect_map _ _ hF, pstar_eq_reflect_map _ _ hG, reflect_mul F G hF hG, Polynomial.map_mul]

/-- `(cH)* = c̄ H*`. -/
theorem pstar_C_mul (n : ℕ) (c : ℂ) (H : ℂ[X]) : pstar n (C c * H) = C (conj c) * pstar n H := by
  ext k
  rw [coeff_pstar, coeff_C_mul, coeff_C_mul, coeff_pstar]
  split_ifs <;> simp

end Sheil
