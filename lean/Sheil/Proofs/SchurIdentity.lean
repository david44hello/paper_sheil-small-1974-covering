/- Sheil/Proofs/SchurIdentity.lean — proofs of the row schurCohn_unique of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Defs.Basic

namespace Sheil.Proofs

open Polynomial ComplexConjugate Finset

/-! ## The entry formula on natural indices -/

/-- The Schur-Cohn entry formula on all natural indices; on `Fin n` it is `schurCohn` (by `rfl`). -/
noncomputable def scEntry (n : ℕ) (H : ℂ[X]) (a b : ℕ) : ℂ :=
  ∑ r ∈ range (min a b + 1),
    (H.coeff (a - r) * conj (H.coeff (b - r)) - conj (H.coeff (n - a + r)) * H.coeff (n - b + r))

/-- The coefficient of `z^a conj(η)^b` in `H(z) conj H(η) - H*(z) conj H*(η)`. -/
noncomputable def scDiff (n : ℕ) (H : ℂ[X]) (a b : ℕ) : ℂ :=
  H.coeff a * conj (H.coeff b) - conj (H.coeff (n - a)) * H.coeff (n - b)

theorem schurCohn_eq_scEntry (n : ℕ) (H : ℂ[X]) (i j : Fin n) :
    schurCohn n H i j = scEntry n H i j := rfl

theorem scEntry_zero_left (n : ℕ) (H : ℂ[X]) (b : ℕ) : scEntry n H 0 b = scDiff n H 0 b := by
  simp [scEntry, scDiff]

theorem scEntry_zero_right (n : ℕ) (H : ℂ[X]) (a : ℕ) : scEntry n H a 0 = scDiff n H a 0 := by
  simp [scEntry, scDiff]

/-- The recurrence of P025_body.tex:250, `K_{ij} - K_{i-1,j-1} = h_i conj(h_j) - conj(h_{n-i}) h_{n-j}`. -/
theorem scEntry_succ (n : ℕ) (H : ℂ[X]) {a b : ℕ} (ha : a < n) (hb : b < n) :
    scEntry n H (a + 1) (b + 1) = scEntry n H a b + scDiff n H (a + 1) (b + 1) := by
  unfold scEntry scDiff
  rw [show min (a + 1) (b + 1) + 1 = min a b + 1 + 1 by omega, sum_range_succ']
  -- `congr 1` closes the `r = 0` term (`scDiff`) by `rfl`; the shifted sum remains.
  congr 1
  refine sum_congr rfl fun r _ => ?_
  have h1 : n - (a + 1) + (r + 1) = n - a + r := by omega
  have h2 : n - (b + 1) + (r + 1) = n - b + r := by omega
  simp only [h1, h2, Nat.add_sub_add_right]

/-- Row `n` of the extended formula vanishes (the top boundary). -/
theorem scEntry_top_left (n : ℕ) (H : ℂ[X]) {b : ℕ} (hb : b ≤ n) : scEntry n H n b = 0 := by
  unfold scEntry
  rw [min_eq_right hb, sum_sub_distrib, sub_eq_zero,
    ← sum_range_reflect (fun r => H.coeff (n - r) * conj (H.coeff (b - r))) (b + 1)]
  refine sum_congr rfl fun r hr => ?_
  have hr' : r ≤ b := Nat.lt_succ_iff.mp (mem_range.mp hr)
  have e1 : n - (b + 1 - 1 - r) = n - b + r := by omega
  have e2 : b - (b + 1 - 1 - r) = r := by omega
  have e3 : n - n + r = r := by omega
  simp only [e1, e2, e3]
  ring

/-- Column `n` of the extended formula vanishes (the right boundary). -/
theorem scEntry_top_right (n : ℕ) (H : ℂ[X]) {a : ℕ} (ha : a ≤ n) : scEntry n H a n = 0 := by
  unfold scEntry
  rw [min_eq_left ha, sum_sub_distrib, sub_eq_zero,
    ← sum_range_reflect (fun r => H.coeff (a - r) * conj (H.coeff (n - r))) (a + 1)]
  refine sum_congr rfl fun r hr => ?_
  have hr' : r ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hr)
  have e1 : a - (a + 1 - 1 - r) = r := by omega
  have e2 : n - (a + 1 - 1 - r) = n - a + r := by omega
  have e3 : n - n + r = r := by omega
  simp only [e1, e2, e3]
  ring

/-! ## Double sums over `range` -/

/-- Split off the index `0` in both variables. -/
theorem sum_split (m : ℕ) (f : ℕ → ℕ → ℂ) (z w : ℂ) :
    ∑ a ∈ range (m + 1), ∑ b ∈ range (m + 1), f a b * z ^ a * w ^ b =
      ∑ a ∈ range m, (∑ b ∈ range m, f (a + 1) (b + 1) * z ^ (a + 1) * w ^ (b + 1) +
        f (a + 1) 0 * z ^ (a + 1) * w ^ 0) + ∑ b ∈ range (m + 1), f 0 b * z ^ 0 * w ^ b := by
  rw [sum_range_succ']
  congr 1
  exact sum_congr rfl fun a _ => sum_range_succ' _ _

/-- Multiplication by `z w` shifts both exponents. -/
theorem mul_sum_shift (m : ℕ) (f : ℕ → ℕ → ℂ) (z w : ℂ) :
    z * w * ∑ a ∈ range m, ∑ b ∈ range m, f a b * z ^ a * w ^ b =
      ∑ a ∈ range m, ∑ b ∈ range m, f a b * z ^ (a + 1) * w ^ (b + 1) := by
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  ring

/-- The `n × n` double sum equals the `(n+1) × (n+1)` one: row `n` and column `n` vanish. -/
theorem form_eq_succ (n : ℕ) (H : ℂ[X]) (z w : ℂ) :
    ∑ a ∈ range n, ∑ b ∈ range n, scEntry n H a b * z ^ a * w ^ b =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), scEntry n H a b * z ^ a * w ^ b := by
  rw [sum_range_succ _ n]
  have htop : ∑ b ∈ range (n + 1), scEntry n H n b * z ^ n * w ^ b = 0 :=
    sum_eq_zero fun b hb => by
      rw [scEntry_top_left n H (Nat.lt_succ_iff.mp (mem_range.mp hb))]
      ring
  rw [htop, add_zero]
  refine sum_congr rfl fun a ha => ?_
  rw [sum_range_succ _ n, scEntry_top_right n H (le_of_lt (mem_range.mp ha))]
  ring

/-- The core identity with `w` in place of `conj η`; no degree hypothesis is needed here. -/
theorem core_identity (n : ℕ) (H : ℂ[X]) (z w : ℂ) :
    (1 - z * w) * ∑ a ∈ range n, ∑ b ∈ range n, scEntry n H a b * z ^ a * w ^ b =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), scDiff n H a b * z ^ a * w ^ b := by
  have h1 := form_eq_succ n H z w
  have h2 := sum_split n (scEntry n H) z w
  have h3 := mul_sum_shift n (scEntry n H) z w
  have h7 := sum_split n (scDiff n H) z w
  have h4 : ∑ a ∈ range n, (∑ b ∈ range n, scEntry n H (a + 1) (b + 1) * z ^ (a + 1) * w ^ (b + 1) +
        scEntry n H (a + 1) 0 * z ^ (a + 1) * w ^ 0) =
      ∑ a ∈ range n, (∑ b ∈ range n, scDiff n H (a + 1) (b + 1) * z ^ (a + 1) * w ^ (b + 1) +
        scDiff n H (a + 1) 0 * z ^ (a + 1) * w ^ 0) +
      ∑ a ∈ range n, ∑ b ∈ range n, scEntry n H a b * z ^ (a + 1) * w ^ (b + 1) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a ha => ?_
    have hinner : ∑ b ∈ range n, scEntry n H (a + 1) (b + 1) * z ^ (a + 1) * w ^ (b + 1) =
        ∑ b ∈ range n, scDiff n H (a + 1) (b + 1) * z ^ (a + 1) * w ^ (b + 1) +
        ∑ b ∈ range n, scEntry n H a b * z ^ (a + 1) * w ^ (b + 1) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun b hb => ?_
      rw [scEntry_succ n H (mem_range.mp ha) (mem_range.mp hb)]
      ring
    rw [hinner, scEntry_zero_right]
    ring
  have h5 : ∑ b ∈ range (n + 1), scEntry n H 0 b * z ^ 0 * w ^ b =
      ∑ b ∈ range (n + 1), scDiff n H 0 b * z ^ 0 * w ^ b :=
    sum_congr rfl fun b _ => by rw [scEntry_zero_left]
  linear_combination h1 + h2 - h3 + h4 + h5 - h7

/-! ## The two sides as double sums -/

theorem schurCohnForm_eq_range (n : ℕ) (H : ℂ[X]) (z eta : ℂ) :
    schurCohnForm n H z eta =
      ∑ a ∈ range n, ∑ b ∈ range n, scEntry n H a b * z ^ a * conj eta ^ b := by
  have hinner : ∀ i : Fin n, ∑ j : Fin n, schurCohn n H i j * z ^ (i : ℕ) * conj eta ^ (j : ℕ) =
      ∑ b ∈ range n, scEntry n H i b * z ^ (i : ℕ) * conj eta ^ b := fun i =>
    Fin.sum_univ_eq_sum_range (fun b => scEntry n H i b * z ^ (i : ℕ) * conj eta ^ b) n
  unfold schurCohnForm
  simp only [hinner]
  exact Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range n, scEntry n H a b * z ^ a * conj eta ^ b) n

theorem eval_eq_range (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (z : ℂ) :
    H.eval z = ∑ a ∈ range (n + 1), H.coeff a * z ^ a :=
  eval_eq_sum_range' (Nat.lt_succ_of_le hdeg) z

theorem conj_eval_eq_range (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (eta : ℂ) :
    conj (H.eval eta) = ∑ b ∈ range (n + 1), conj (H.coeff b) * conj eta ^ b := by
  rw [eval_eq_range n H hdeg eta, map_sum]
  simp only [map_mul, map_pow]

theorem pstar_eval_range (n : ℕ) (H : ℂ[X]) (z : ℂ) :
    (pstar n H).eval z = ∑ a ∈ range (n + 1), conj (H.coeff (n - a)) * z ^ a := by
  unfold pstar
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

theorem conj_pstar_eval_range (n : ℕ) (H : ℂ[X]) (eta : ℂ) :
    conj ((pstar n H).eval eta) = ∑ b ∈ range (n + 1), H.coeff (n - b) * conj eta ^ b := by
  rw [pstar_eval_range n H eta, map_sum]
  simp only [map_mul, map_pow, Complex.conj_conj]

theorem rhs_eq_range (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (z eta : ℂ) :
    H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta) =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), scDiff n H a b * z ^ a * conj eta ^ b := by
  rw [eval_eq_range n H hdeg z, conj_eval_eq_range n H hdeg eta, pstar_eval_range n H z,
    conj_pstar_eval_range n H eta, sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  unfold scDiff
  ring

/-! ## Target 1: the multiplied identity, for every `z, η` -/

/-- Lemma 2.2(b), multiplied form (P025_body.tex:203-208): for `deg H ≤ n` and EVERY `z, η ∈ ℂ`,
`(1 - z η̄) Σ_{i,j<n} K_{ij} z^i η̄^j = H(z) conj H(η) - H*(z) conj H*(η)`. No hypothesis on the zeros of `H`. -/
theorem schurCohn_identity (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (z eta : ℂ) :
    (1 - z * conj eta) * schurCohnForm n H z eta =
      H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta) := by
  rw [schurCohnForm_eq_range, rhs_eq_range n H hdeg z eta]
  exact core_identity n H z (conj eta)

/-! ## Target 2: uniqueness of the coefficient matrix -/

theorem coeff_finSum (n : ℕ) (c : Fin n → ℂ) (i : Fin n) :
    (∑ j : Fin n, C (c j) * X ^ (j : ℕ)).coeff i = c i := by
  rw [finsetSum_coeff, sum_eq_single i]
  · simp
  · intro j _ hji
    rw [coeff_C_mul_X_pow]
    exact ite_eq_right_iff.mpr fun h => absurd (Fin.ext h).symm hji
  · intro hi
    exact absurd (mem_univ i) hi

theorem eval_finSum (n : ℕ) (c : Fin n → ℂ) (z : ℂ) :
    (∑ j : Fin n, C (c j) * X ^ (j : ℕ)).eval z = ∑ j : Fin n, c j * z ^ (j : ℕ) := by
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

/-- If `(1 - z w) Σ_j c_j z^j = 0` for every `z`, then every `c_j = 0`. -/
theorem eq_zero_of_mul_eval (n : ℕ) (w : ℂ) (c : Fin n → ℂ)
    (h : ∀ z : ℂ, (1 - z * w) * ∑ j : Fin n, c j * z ^ (j : ℕ) = 0) : c = 0 := by
  have hne : (1 - C w * X : ℂ[X]) ≠ 0 := by
    intro h0
    have := congrArg (eval 0) h0
    simp at this
  have hQ0 : (∑ j : Fin n, C (c j) * X ^ (j : ℕ) : ℂ[X]) = 0 := by
    have hprod : (1 - C w * X) * (∑ j : Fin n, C (c j) * X ^ (j : ℕ)) = 0 := by
      apply Polynomial.funext
      intro z
      rw [eval_mul, eval_finSum, eval_zero, eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_comm w z]
      exact h z
    exact (mul_eq_zero.mp hprod).resolve_left hne
  funext i
  rw [Pi.zero_apply, ← coeff_finSum n c i, hQ0, coeff_zero]

/-- If `Σ_j c_j u^j = 0` for every `u`, then every `c_j = 0`. -/
theorem eq_zero_of_eval (n : ℕ) (c : Fin n → ℂ) (h : ∀ u : ℂ, ∑ j : Fin n, c j * u ^ (j : ℕ) = 0) :
    c = 0 :=
  eq_zero_of_mul_eval n 0 c fun z => by rw [mul_zero, sub_zero, one_mul]; exact h z

/-- Uniqueness (row `schurCohn_unique` of Paper/Statements.lean, exact type): any `Fin n` matrix satisfying the
multiplied identity for all `z, η` is the Schur-Cohn matrix. -/
theorem schurCohn_unique_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : ∀ z eta : ℂ, (1 - z * conj eta) * (∑ i : Fin n, ∑ j : Fin n, K i j * z ^ (i : ℕ) * conj eta ^ (j : ℕ)) =
      H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta)) :
    K = schurCohn n H := by
  have hD : ∀ z eta : ℂ, (1 - z * conj eta) *
      ∑ i : Fin n, (∑ j : Fin n, (K i j - schurCohn n H i j) * conj eta ^ (j : ℕ)) * z ^ (i : ℕ) = 0 := by
    intro z eta
    have hS := schurCohn_identity n H hdeg z eta
    unfold schurCohnForm at hS
    have hsplit : ∑ i : Fin n, (∑ j : Fin n, (K i j - schurCohn n H i j) * conj eta ^ (j : ℕ)) * z ^ (i : ℕ) =
        (∑ i : Fin n, ∑ j : Fin n, K i j * z ^ (i : ℕ) * conj eta ^ (j : ℕ)) -
          ∑ i : Fin n, ∑ j : Fin n, schurCohn n H i j * z ^ (i : ℕ) * conj eta ^ (j : ℕ) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_sub_distrib, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit, mul_sub, hK z eta, hS, sub_self]
  have hrow : ∀ eta : ℂ, ∀ i : Fin n,
      ∑ j : Fin n, (K i j - schurCohn n H i j) * conj eta ^ (j : ℕ) = 0 := by
    intro eta
    have hc := eq_zero_of_mul_eval n (conj eta)
      (fun i => ∑ j : Fin n, (K i j - schurCohn n H i j) * conj eta ^ (j : ℕ)) (fun z => hD z eta)
    exact fun i => congrFun hc i
  ext i j
  have hrowi := eq_zero_of_eval n (fun j => K i j - schurCohn n H i j) fun u => by
    have hu := hrow (conj u) i
    rw [Complex.conj_conj] at hu
    exact hu
  exact sub_eq_zero.mp (congrFun hrowi j)

#print axioms schurCohn_identity
#print axioms schurCohn_unique_proved

end Sheil.Proofs
