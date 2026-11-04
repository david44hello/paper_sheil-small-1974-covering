/- Sheil/Defs/Basic.lean — definitions (unitDisc, discImage, pstar, coefMax, coefMaxDeg, maxMod, normalizeAt, SelfInversive, ...).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Mathlib

namespace Sheil

open Polynomial ComplexConjugate

/-- The open unit disc `𝔻 = {z ∈ ℂ : |z| < 1}` (P025_body.tex:39). -/
def unitDisc : Set ℂ := Metric.ball (0 : ℂ) 1

/-- The image `P(𝔻)` of the open unit disc under the polynomial `P`. -/
def discImage (P : ℂ[X]) : Set ℂ := (fun z => P.eval z) '' unitDisc

/-- `H*(z) = z^n conj(H(1/z̄)) = Σ_{k=0}^{n} conj(h_{n-k}) z^k` for a polynomial of degree at most `n`
(P025_body.tex:43 and 162-163; the coefficient `h_n` may vanish). Defined by its coefficient formula;
row `pstar_eval` proves the formula `z^n conj(H(1/z̄))`. -/
noncomputable def pstar (n : ℕ) (H : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (conj (H.coeff (n - k))) * X ^ k

/-- `A = max_{0 ≤ k ≤ n} |a_k|` (P025_body.tex:42, 339). -/
noncomputable def coefMax (n : ℕ) (P : ℂ[X]) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => ‖P.coeff k‖)

/-- `A(P) = max_k |a_k|` with `n` the degree of `P` (P025_body.tex:42). -/
noncomputable def coefMaxDeg (P : ℂ[X]) : ℝ := coefMax P.natDegree P

/-- `M(P) = max_{|z|=1} |P(z)|` (P025_body.tex:42), written as a supremum; row `exists_max_circle` proves it is
attained. -/
noncomputable def maxMod (P : ℂ[X]) : ℝ :=
  sSup ((fun z => ‖P.eval z‖) '' Metric.sphere (0 : ℂ) 1)

/-- The normalization of Theorem 4.1, Case 2 (P025_body.tex:355-357): `P(αz)/a_0`. -/
noncomputable def normalizeAt (P : ℂ[X]) (alpha : ℂ) : ℂ[X] :=
  C (P.coeff 0)⁻¹ * P.comp (C alpha * X)

/-- Self-inversive (P025_body.tex:40, 45): degree `n ≥ 1` and `P* = λ P` for some `|λ| = 1`, with `n = deg P`. -/
def SelfInversive (P : ℂ[X]) : Prop :=
  1 ≤ P.natDegree ∧ ∃ lam : ℂ, ‖lam‖ = 1 ∧ pstar P.natDegree P = C lam * P

/-- All zeros of `P` lie on the unit circle. (For `P = 0` this fails: every point is a zero.) -/
def ZerosOnCircle (P : ℂ[X]) : Prop := ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1

/-- Condition (eq:mirror), P025_body.tex:336-338: `|a_k| = |a_{n-k}|` for `0 ≤ k ≤ n`. -/
def Mirror (n : ℕ) (P : ℂ[X]) : Prop := ∀ k ≤ n, ‖P.coeff k‖ = ‖P.coeff (n - k)‖

/-- The literal reading of Problem 4.24 in coefficient form (P025_body.tex:98, 107, 172-173):
`a_{n-k} = ε a_k` for every `k ≤ n`, with `ε ∈ {1, -1}`. -/
def PlusMinusPalindromic (n : ℕ) (P : ℂ[X]) : Prop :=
  ∃ eps : ℂ, (eps = 1 ∨ eps = -1) ∧ ∀ k ≤ n, P.coeff (n - k) = eps * P.coeff k

/-- Zeros symmetric under `ζ ↦ 1/ζ̄`, with multiplicities (P025_body.tex:46-47, 170). Used with `P(0) ≠ 0`. -/
def ZerosSymmConjInv (P : ℂ[X]) : Prop :=
  ∀ ζ : ℂ, P.rootMultiplicity ζ = P.rootMultiplicity (conj ζ)⁻¹

/-- Zeros symmetric under `ζ ↦ 1/ζ`, with multiplicities (P025_body.tex:56, 172). Used with `P(0) ≠ 0`. -/
def ZerosSymmInv (P : ℂ[X]) : Prop :=
  ∀ ζ : ℂ, P.rootMultiplicity ζ = P.rootMultiplicity ζ⁻¹

/-- The Schur-Cohn matrix `(K_{ij})_{0 ≤ i,j ≤ n-1}` of Lemma 2.2(b) (P025_body.tex:203-208), by the explicit formula
`K_{ij} = Σ_{r=0}^{min(i,j)} (h_{i-r} conj(h_{j-r}) - conj(h_{n-i+r}) h_{n-j+r})`, the solution of the recursion
`K_{ij} - K_{i-1,j-1} = h_i conj(h_j) - conj(h_{n-i}) h_{n-j}` of P025_body.tex:250. Row `lem_2_2_b` proves that it is
the coefficient matrix of `K(z,η) = (H(z) conj H(η) - H*(z) conj H*(η)) / (1 - z η̄)`. -/
noncomputable def schurCohn (n : ℕ) (H : ℂ[X]) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ r ∈ Finset.range (min (i : ℕ) j + 1),
    (H.coeff (i - r) * conj (H.coeff (j - r)) - conj (H.coeff (n - i + r)) * H.coeff (n - j + r))

/-- The double sum `Σ_{i,j=0}^{n-1} K_{ij} z^i η̄^j` of Lemma 2.2(b) (P025_body.tex:206). -/
noncomputable def schurCohnForm (n : ℕ) (H : ℂ[X]) (z eta : ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, schurCohn n H i j * z ^ (i : ℕ) * conj eta ^ (j : ℕ)

/-- The note after Theorem 3.4 (P025_body.tex:314-316, `m = n/2`): `T_c(θ) = c e^{-imθ} P(e^{iθ})`, defined for complex
`θ`. With `c = 1` it is the paper's `Q(θ) = e^{-imθ} P(e^{iθ})`; the paper's `T = cQ` is `trigT c`. -/
noncomputable def trigT (c : ℂ) (m : ℕ) (P : ℂ[X]) (θ : ℂ) : ℂ :=
  c * Complex.exp (-(m : ℂ) * θ * Complex.I) * P.eval (Complex.exp (θ * Complex.I))

end Sheil
