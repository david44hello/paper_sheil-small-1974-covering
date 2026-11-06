/-
Sheil/Paper/Statements.lean — one Lean theorem per claim of the paper "Sheil-Small's (1974) covering problem has a
positive answer" (Dave Goel), and the retired row `fig1_regions`. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
Rows are named by the paper's numbering; each docstring gives the claim's lines "P025_body.tex:<line>" of the paper's
TeX source. Every row is proved; the status of each row, as Lean reports it, is in AUDIT.md, the printed claims are
mapped to rows in CLAIM_MAP.tsv, and the modelling choices are in AUDIT_NOTES.md.
-/
import Sheil.Defs.Basic
import Sheil.Defs.Examples
import Sheil.Cited.CoefHalfMax
import Sheil.Proofs.Lemma21
import Sheil.Proofs.Lemma22
import Sheil.Proofs.Sec3
import Sheil.Proofs.Sec4
import Sheil.Proofs.SchurIdentity
import Sheil.Proofs.Rows
import Sheil.Proofs.ExSmall
import Sheil.Proofs.ExCardioid
import Sheil.Proofs.Ex52
import Sheil.Proofs.ExLimacon
import Sheil.Proofs.MaxPoint
import Sheil.Proofs.Factor
import Sheil.Proofs.GramPSD
import Sheil.Proofs.PstarDeriv
import Sheil.Proofs.TrigNote
import Sheil.Proofs.Fig2Grey
import Sheil.Proofs.Fig1Example

namespace Sheil.Paper

open Sheil Polynomial ComplexConjugate
-- Mathlib's order on ℂ (0 ≤ z iff z is real and ≥ 0), needed by `Matrix.PosSemidef`.
open scoped ComplexOrder

/-! ## Section 1 and the running text of Section 2 -/

/-- P025_body.tex:43 and 163: "`H*(z) = z^n conj(H(1/z̄))`" for `H` of degree at most `n` (at `z ≠ 0`). -/
theorem pstar_eval (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (z : ℂ) (hz : z ≠ 0) :
    (pstar n H).eval z = z ^ n * conj (H.eval (conj z)⁻¹) := Proofs.pstar_eval_proved n H hdeg z hz

/-- P025_body.tex:164: "`(H*)* = H`". -/
theorem pstar_pstar (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) : pstar n (pstar n H) = H :=
  Proofs.pstar_pstar_proved n H hdeg

/-- P025_body.tex:164: "`|H*(z)| = |H(z)|` when `|z| = 1`". -/
theorem pstar_norm_circle (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(pstar n H).eval z‖ = ‖H.eval z‖ := Proofs.pstar_norm_circle_proved n H hdeg z hz

/-- P025_body.tex:48-49: "Sheil-Small's book requires `λ = 1`; every self-inversive polynomial satisfies this after
multiplication by a suitable constant of modulus 1": `P* = λP` with `|λ| = 1` for some `λ` iff `(μP)* = μP` for some
`|μ| = 1`. -/
theorem intro_normalize_lambda (n : ℕ) (P : ℂ[X]) :
    (∃ lam : ℂ, ‖lam‖ = 1 ∧ pstar n P = C lam * P) ↔
      ∃ mu : ℂ, ‖mu‖ = 1 ∧ pstar n (C mu * P) = C mu * P := intro_normalize_lambda_proved n P

/-- P025_body.tex:106-108: "`1 + 3iz + z^2` is of this kind [`a_{n-k} = ±a_k`] but is not self-inversive". -/
theorem intro_ex_three_i :
    polyThreeI.natDegree = 2 ∧ PlusMinusPalindromic 2 polyThreeI ∧ ¬ SelfInversive polyThreeI :=
  intro_ex_three_i_proved

/-- P025_body.tex:129-131: "For self-inversive `P` the disc of radius `M/2` still exists (Proposition 3.3), but `M/2` may be smaller than
`A`: for `1 + 4z + z^2` we have `M/2 = 3` and `A = 4`"; also Figure 2's label "`1+4z+z^2`: `A=4`, `M=6`"
(P025_body.tex:424). -/
theorem intro_ex_four :
    SelfInversive polyFour ∧ maxMod polyFour / 2 = 3 ∧ coefMaxDeg polyFour = 4 := intro_ex_four_proved

/-- Abstract P025_body.tex:15-16: a non-constant `P` maps `𝔻` onto a DOMAIN (open and connected). -/
theorem abs_domain (P : ℂ[X]) (hnc : 0 < P.natDegree) : IsOpen (discImage P) ∧ IsConnected (discImage P) :=
  abs_domain_proved P hnc

/-- Abstract P025_body.tex:21-22: "the question is therefore equivalent to asking whether every coefficient
has modulus at most half this maximum": `M ≥ 2A` iff `|a_k| ≤ M/2` for every `k`. -/
theorem abs_M_two_A_iff (P : ℂ[X]) :
    2 * coefMaxDeg P ≤ maxMod P ↔ ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2 := abs_M_two_A_iff_proved P

/-! The abstract's covering rows (abs_self_inversive, abs_zeros_conj_inv, abs_zeros_inv, abs_plus_minus) and
intro_covering_implies_coef stand at the END of this file: Lean needs the rows they rest on (thm_3_1, thm_4_1) first. -/

/-! ## Figure 1 (P025_body.tex:93-104). Row `fig1_example` stands at the END of this file: it rests on `thm_4_1`. -/

/-- Figure 1: both symmetry classes lie in the class (eq:mirror), and the circle class lies in the self-inversive class
(caption P025_body.tex:97-99; Lemma 2.1). -/
theorem fig1_inclusions :
    (∀ P : ℂ[X], SelfInversive P → Mirror P.natDegree P) ∧
    (∀ P : ℂ[X], PlusMinusPalindromic P.natDegree P → Mirror P.natDegree P) ∧
    (∀ P : ℂ[X], 1 ≤ P.natDegree → ZerosOnCircle P → SelfInversive P) := fig1_inclusions_proved

/-- RETIRED: the regions of an earlier Figure 1, no longer printed. Kept as a Lean example, not counted. Witnesses that
separate the classes: `1 + z^2` is in all three; `z - i` has all zeros on the circle and is not `a_{n-k} = ±a_k`; `1 + 4z + z^2` is self-inversive and `a_{n-k} = ±a_k`
with not all zeros on the circle; `z^2 - (5/2) i z - 1` is self-inversive only; `1 + 3iz + z^2` is `a_{n-k} = ±a_k` only; `1 + z + i z^2`
has only condition (eq:mirror). -/
theorem fig1_regions :
    (SelfInversive polyOnePlusSq ∧ PlusMinusPalindromic 2 polyOnePlusSq ∧ ZerosOnCircle polyOnePlusSq) ∧
    (polyXSubI.natDegree = 1 ∧ ZerosOnCircle polyXSubI ∧ ¬ PlusMinusPalindromic 1 polyXSubI) ∧
    (SelfInversive polyFour ∧ PlusMinusPalindromic 2 polyFour ∧ ¬ ZerosOnCircle polyFour) ∧
    (SelfInversive polySelfInvOnly ∧ ¬ PlusMinusPalindromic 2 polySelfInvOnly ∧ ¬ ZerosOnCircle polySelfInvOnly) ∧
    (PlusMinusPalindromic 2 polyThreeI ∧ ¬ SelfInversive polyThreeI) ∧
    (polyMirrorOnly.natDegree = 2 ∧ Mirror 2 polyMirrorOnly ∧ ¬ SelfInversive polyMirrorOnly ∧
      ¬ PlusMinusPalindromic 2 polyMirrorOnly) := fig1_regions_proved

/-! ## Section 2: Lemma 2.1 and Lemma 2.2 -/

/-- Lemma 2.1(a), P025_body.tex:168, 170-171. -/
theorem lem_2_1_a (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree = n) (h0 : P.eval 0 ≠ 0) :
    (ZerosSymmConjInv P ↔ ∃ lam : ℂ, ‖lam‖ = 1 ∧ pstar n P = C lam * P) ∧
    ∀ lam : ℂ, pstar n P = C lam * P → ∀ k ≤ n, conj (P.coeff (n - k)) = lam * P.coeff k :=
  lem_2_1_a_proved n P hdeg h0

/-- Lemma 2.1(b), P025_body.tex:168, 172-173 (one `ε` for all `k`). -/
theorem lem_2_1_b (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree = n) (h0 : P.eval 0 ≠ 0) :
    ZerosSymmInv P ↔ PlusMinusPalindromic n P := lem_2_1_b_proved n P hdeg h0

/-- Lemma 2.1, P025_body.tex:175: "In both cases `|a_k| = |a_{n-k}|` for every `k`." -/
theorem lem_2_1_mirror (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree = n) (h0 : P.eval 0 ≠ 0)
    (hsym : ZerosSymmConjInv P ∨ ZerosSymmInv P) : Mirror n P := lem_2_1_mirror_proved n P hdeg h0 hsym

/-- Lemma 2.1, P025_body.tex:175-176 (proof P025_body.tex:187): "Every polynomial of degree `n ≥ 1` with all its zeros
on the unit circle is self-inversive." -/
theorem lem_2_1_circle (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) : SelfInversive P :=
  lem_2_1_circle_proved P hdeg hz

/-- Lemma 2.2, eq. (eq:factor), P025_body.tex:195-199: `β_1, …, β_n` with `|β_l| ≤ 1`, `H = h_0 ∏ (1 - β̄_l z)`,
`H* = h̄_0 ∏ (z - β_l)`. -/
theorem lem_2_2_factor (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0) :
    ∃ beta : Fin n → ℂ, (∀ l, ‖beta l‖ ≤ 1) ∧
      (∀ z : ℂ, H.eval z = H.coeff 0 * ∏ l, (1 - conj (beta l) * z)) ∧
      (∀ z : ℂ, (pstar n H).eval z = conj (H.coeff 0) * ∏ l, (z - beta l)) :=
  Proofs.lem_2_2_factor_proved n H hdeg hD

/-- Lemma 2.2(a), P025_body.tex:202: `|zH'(z)| ≤ |nH(z) - zH'(z)|` on the unit circle. -/
theorem lem_2_2_a (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z * H.derivative.eval z‖ ≤ ‖(n : ℂ) * H.eval z - z * H.derivative.eval z‖ :=
  Proofs.lem_2_2_a_proved n H hdeg hD z hz

/-- P025_body.tex:190 (claim N1): "Part (a) is a classical inequality (on `|z|=1` it says `|H'(z)| ≤ |(H^*)'(z)|` ...)",
for `H` of degree at most `n` with no zero in `𝔻` (the hypotheses of Lemma 2.2) and `|z| = 1`. -/
theorem lem_2_2_a_pstar (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖H.derivative.eval z‖ ≤ ‖(pstar n H).derivative.eval z‖ :=
  Proofs.lem_2_2_a_pstar_proved n H hdeg hD z hz

/-- P025_body.tex:230: "At a zero of `H` on the circle the inequality in (a) is an equality" (proved at every zero). -/
theorem lem_2_2_a_zero (n : ℕ) (H : ℂ[X]) (z : ℂ) (hz0 : H.eval z = 0) :
    ‖z * H.derivative.eval z‖ = ‖(n : ℂ) * H.eval z - z * H.derivative.eval z‖ :=
  Proofs.lem_2_2_a_zero_proved n H z hz0

/-- Eq. (eq:one-factor), P025_body.tex:232-235 ("one checks by multiplying out"; proved for every `β`). -/
theorem eq_one_factor (beta z eta : ℂ) :
    (1 - conj beta * z) * (1 - beta * conj eta) - (z - beta) * (conj eta - conj beta) =
      ((1 - ‖beta‖ ^ 2 : ℝ) : ℂ) * (1 - z * conj eta) := Proofs.eq_one_factor_proved beta z eta

/-- Lemma 2.2(b), P025_body.tex:203-208: `K(z,η) = (H(z) conj H(η) - H*(z) conj H*(η)) / (1 - z η̄) = Σ K_ij z^i η̄^j`
— multiplied out for all `z, η`, and as a quotient where `z η̄ ≠ 1` — and `(K_ij)` is positive semidefinite. -/
theorem lem_2_2_b (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0) :
    (∀ z eta : ℂ, (1 - z * conj eta) * schurCohnForm n H z eta =
      H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta)) ∧
    (∀ z eta : ℂ, z * conj eta ≠ 1 → schurCohnForm n H z eta =
      (H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta)) / (1 - z * conj eta)) ∧
    (schurCohn n H).PosSemidef := Proofs.lem_2_2_b_proved n H hdeg hD

/-- Support for Lemma 2.2(b) ("its coefficient matrix", P025_body.tex:208): the identity of `lem_2_2_b` determines the
matrix, so `schurCohn` IS the coefficient matrix of `K(z,η)` (no hypothesis on the zeros). -/
theorem schurCohn_unique (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n) (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : ∀ z eta : ℂ, (1 - z * conj eta) * (∑ i : Fin n, ∑ j : Fin n, K i j * z ^ (i : ℕ) * conj eta ^ (j : ℕ)) =
      H.eval z * conj (H.eval eta) - (pstar n H).eval z * conj ((pstar n H).eval eta)) :
    K = schurCohn n H := Proofs.schurCohn_unique_proved n H hdeg K hK

/-- Lemma 2.2(c), eq. (eq:entries), P025_body.tex:209-213 (no hypothesis on the zeros needed). -/
theorem lem_2_2_c (n : ℕ) (H : ℂ[X]) (j : Fin n) :
    schurCohn n H j j = ∑ r ∈ Finset.range ((j : ℕ) + 1), ((‖H.coeff r‖ ^ 2 - ‖H.coeff (n - r)‖ ^ 2 : ℝ) : ℂ) ∧
    schurCohn n H ⟨0, Nat.zero_lt_of_lt j.isLt⟩ j =
      H.coeff 0 * conj (H.coeff j) - conj (H.coeff n) * H.coeff (n - j) := Proofs.lem_2_2_c_proved n H j

/-! ## Section 3 -/

/-- Support (P025_body.tex:42, 259: "let `|ζ| = 1` with `|P(ζ)| = M(P)`"): `M(P)` is attained on the circle. -/
theorem exists_max_circle (P : ℂ[X]) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ‖P.eval ζ‖ = maxMod P :=
  Proofs.exists_max_circle_proved P

/-- Theorem 3.1, P025_body.tex:258-262 (open discs); also P025_body.tex:125 ("In Theorem 3.1, that no open disc of radius
larger than `M/2` lies in `P(𝔻)` is elementary": this row uses no cited result). -/
theorem thm_3_1 (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hM : ‖P.eval ζ‖ = maxMod P) :
    Metric.ball (P.eval ζ / 2) (maxMod P / 2) ⊆ discImage P ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage P → r ≤ maxMod P / 2) ∧
    ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔ 2 * coefMaxDeg P ≤ maxMod P) :=
  Proofs.thm_3_1_proved P hdeg hz ζ hζ hM

/-- Lemma 3.2, P025_body.tex:269-272 ("it also covers polynomials of degree less than `n`", P025_body.tex:267). -/
theorem lem_3_2 (n : ℕ) (hn : 1 ≤ n) (f : ℂ[X]) (hdeg : f.natDegree ≤ n) (z0 : ℂ) (hz0 : ‖z0‖ = 1)
    (hf' : f.derivative.eval z0 ≠ 0) :
    Metric.ball (f.eval z0 - z0 * f.derivative.eval z0 / n) (‖f.derivative.eval z0‖ / n) ⊆ discImage f :=
  Proofs.lem_3_2_proved n hn f hdeg z0 hz0 hf'

/-- Support for Lemma 3.2 (P025_body.tex:264-265: de Bruijn's theorem, "quoted in [OR74, p. 332] for open and closed
circular regions"): the CLOSED disc of Lemma 3.2 lies in the image of the closed unit disc. -/
theorem lem_3_2_closed (n : ℕ) (hn : 1 ≤ n) (f : ℂ[X]) (hdeg : f.natDegree ≤ n) (z0 : ℂ) (hz0 : ‖z0‖ = 1)
    (hf' : f.derivative.eval z0 ≠ 0) :
    Metric.closedBall (f.eval z0 - z0 * f.derivative.eval z0 / n) (‖f.derivative.eval z0‖ / n) ⊆
      (fun z => f.eval z) '' Metric.closedBall (0 : ℂ) 1 := Proofs.lem_3_2_closed_proved n hn f hdeg z0 hz0 hf'

/-- Proposition 3.3, P025_body.tex:280-283, with "In particular `F'(ζ) ≠ 0`" (P025_body.tex:292-293); also the Table's
and the introduction's "point `ζ` of maximum modulus, where `ζP'(ζ) = (n/2) P(ζ)`" (P025_body.tex:75-76, 122), and the
sketch's "the first fact, applied at a point `ζ` where `|P|` is largest, places every omitted value at distance at
least `M/2` from `P(ζ)/2`" (P025_body.tex:138-139: the disc below, for every omitted value). -/
theorem prop_3_3 (n : ℕ) (F : ℂ[X]) (hdeg : F.natDegree ≤ n) (hnc : 0 < F.natDegree) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hF : pstar n F = C lam * F) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hM : ‖F.eval ζ‖ = maxMod F) :
    ζ * F.derivative.eval ζ = ((n : ℂ) / 2) * F.eval ζ ∧ F.derivative.eval ζ ≠ 0 ∧
    Metric.ball (F.eval ζ / 2) (maxMod F / 2) ⊆ discImage F :=
  Proofs.prop_3_3_proved n F hdeg hnc lam hlam hF ζ hζ hM

/-- Theorem 3.4 [Kr79, Kr80, OR74, SS74], P025_body.tex:308-311 — the ONE cited result: the Cited/ input
`coef_half_max`, restated with `maxMod` and `ZerosOnCircle` (status CITED). -/
theorem thm_3_4 (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) :
    ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2 := Cited.coef_half_max P hdeg hz

/-- The note after Theorem 3.4, P025_body.tex:313-319 (claim N2; `n = 2m`, `m = n/2`). For `P` of degree `2m ≥ 2` with
all zeros on the unit circle: by Lemma 2.1 `P* = λP` with `|λ| = 1`; for EVERY such `λ`, `Q(θ) = e^{-imθ} P(e^{iθ})`
(`= trigT 1 m P θ`) satisfies `conj Q = λ Q` (real `θ`); a `c` with `c^2 = λ` exists, and for EVERY such `c`,
`T = cQ` (`= trigT c m P`) has `|c| = 1`, is real on the real line, is the trigonometric polynomial
`Σ_{j=0}^{2m} c a_j e^{i(j-m)θ}` (all complex `θ`) of exact degree `m` (top coefficient `c a_n ≠ 0`); its zeros: `P` has
`2m` zeros counted with multiplicity, `T(θ) = 0` iff `P(e^{iθ}) = 0` (complex `θ`), every zero `θ` of `T` is real, and
`t ↦ e^{it}` maps the zeros of `T` in the period `[0, 2π)` one-to-one onto the zeros of `P` ("whose `2m` zeros in a
period are all real"); `max |T| = sup |T| = M(P)`; its constant term `t_0 = (1/2π) ∫_0^{2π} T` is `c a_{n/2}`; and "the
case `k = n/2` says that the constant term `t_0` of such a `T` satisfies `|t_0| ≤ (1/2) max |T|`" (P025_body.tex:318-319):
`|a_m| ≤ M(P)/2` iff `|c a_m| ≤ (1/2) sup |T|`. -/
theorem coef_note_trig (P : ℂ[X]) (m : ℕ) (hm : 1 ≤ m) (hdeg : P.natDegree = 2 * m) (hz : ZerosOnCircle P) :
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
          ‖c * P.coeff m‖ ≤ sSup (Set.range (fun θ : ℝ => ‖trigT c m P θ‖)) / 2) :=
  Proofs.coef_note_trig_proved P m hm hdeg hz

/-- Corollary 3.5, P025_body.tex:321-323 (Theorem 3.1 with Theorem 3.4: this row passes the cited result). -/
theorem cor_3_5 (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P := cor_3_5_of thm_3_1 Cited.coef_half_max P hdeg hz

/-! ## Section 4: Theorem 4.1, its named steps, Remark 4.2 -/

/-- Theorem 4.1 (the covering theorem), P025_body.tex:334-340; abstract P025_body.tex:15-16; Table P025_body.tex:69-70;
P025_body.tex:84-87. Its only input beyond Lean's three standard ones is the cited Theorem 3.4 (the abstract's Lean
sentence, P025_body.tex:30-31: "with the coefficient bound ... taken as given"). -/
theorem thm_4_1 (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree)
    (hmir : Mirror n P) : ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P :=
  thm_4_1_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) cor_3_5 n hn P hdeg hnc hmir

/-- Theorem 4.1, Case 1 (`a_0 = 0`), P025_body.tex:346-353; idea of the proof P025_body.tex:139-140. -/
theorem thm_4_1_case1 (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree)
    (hmir : Mirror n P) (h0 : P.coeff 0 = 0) :
    P.coeff n = 0 ∧ 2 ≤ n ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 1 ∧ ‖P.coeff j‖ = coefMax n P) ∧
    (∀ w ∉ discImage P, w ≠ 0 ∧ coefMax n P ≤ ‖w‖) ∧ Metric.ball 0 (coefMax n P) ⊆ discImage P :=
  thm_4_1_case1_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hnc hmir h0

/-- Theorem 4.1, Case 2, the normalization, P025_body.tex:355-357 (idea P025_body.tex:140: "we normalize so that
`a_0 = a_n = 1`"): `a_n ≠ 0`, `P` has degree `n`; for `|α| = 1` with `α^n = a_0/a_n`, `Q(z) = P(αz)/a_0` has
`q_0 = q_n = 1`, degree at most `n`, (eq:mirror), `Q(𝔻) = P(𝔻)/a_0`, and `A(Q) = A/|a_0| ≥ 1`. -/
theorem thm_4_1_normalize (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 ≠ 0) :
    P.coeff n ≠ 0 ∧ P.natDegree = n ∧
    (∃ alpha : ℂ, ‖alpha‖ = 1 ∧ alpha ^ n = P.coeff 0 / P.coeff n) ∧
    ∀ alpha : ℂ, ‖alpha‖ = 1 → alpha ^ n = P.coeff 0 / P.coeff n →
      (normalizeAt P alpha).coeff 0 = 1 ∧ (normalizeAt P alpha).coeff n = 1 ∧
      (normalizeAt P alpha).natDegree ≤ n ∧ Mirror n (normalizeAt P alpha) ∧
      discImage (normalizeAt P alpha) = (fun w => w / P.coeff 0) '' discImage P ∧
      coefMax n (normalizeAt P alpha) = coefMax n P / ‖P.coeff 0‖ ∧ 1 ≤ coefMax n (normalizeAt P alpha) :=
  thm_4_1_normalize_of n hn P hdeg hmir h0

/-- Theorem 4.1, Case 2 (`a_0 = a_n = 1`), P025_body.tex:359-365; idea P025_body.tex:140-141: every diagonal entry of the
Schur-Cohn matrix of `H = P - w` equals `d = |1 - w|^2 - 1`; for an omitted `w`, `|w - 1| ≥ 1`; if `A = 1`,
`D(1,1) ⊆ P(𝔻)`. -/
theorem thm_4_1_case2_diag (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) :
    (∀ w : ℂ, ∀ j : Fin n, schurCohn n (P - C w) j j = ((‖1 - w‖ ^ 2 - 1 : ℝ) : ℂ)) ∧
    (∀ w ∉ discImage P, 1 ≤ ‖w - 1‖) ∧
    (coefMax n P = 1 → Metric.ball 1 1 ⊆ discImage P) :=
  thm_4_1_case2_diag_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hmir h0 hn1

/-- The idea of the proof, P025_body.tex:140-141 (coverage link): with `a_0 = a_n = 1`, "the diagonal entries `K_jj`
all equal `|1-w|^2-1 ≥ 0`, so `|1-w| ≥ 1`, which gives `D(1,1) ⊂ P(𝔻)`" — every omitted `w` has `|1-w|^2 - 1 ≥ 0` and
`|1-w| ≥ 1`, and `D(1,1) ⊆ P(𝔻)` for EVERY `A`. -/
theorem sketch_disc_one (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) :
    (∀ w ∉ discImage P, 0 ≤ ‖1 - w‖ ^ 2 - 1 ∧ 1 ≤ ‖1 - w‖) ∧ Metric.ball 1 1 ⊆ discImage P :=
  sketch_disc_one_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hmir h0 hn1

/-- Eq. (eq:minor), P025_body.tex:367-372; idea P025_body.tex:142-144: if `A > 1` (with `a_0 = a_n = 1`), `A` is
attained at some `1 ≤ j ≤ n-1`; for every such `j`, `E = a_{n-j}/conj(a_j)` has `|E| = 1` (and does not depend on `w`),
and every omitted `w` (`u = w - 1`) has `A |u + E| ≤ |u|^2 - 1`. -/
theorem eq_minor (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 1 ∧ ‖P.coeff j‖ = coefMax n P) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ‖P.coeff j‖ = coefMax n P →
      ‖P.coeff (n - j) / conj (P.coeff j)‖ = 1 ∧
      ∀ w ∉ discImage P,
        coefMax n P * ‖(w - 1) + P.coeff (n - j) / conj (P.coeff j)‖ ≤ ‖w - 1‖ ^ 2 - 1 :=
  eq_minor_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hmir h0 hn1 hA

/-- Eq. (eq:punctured), P025_body.tex:373-378; idea P025_body.tex:143-144 ("`|w-(1+E)| ≥ A` unless `w = 1-E`.
Consequently every value in `D(1+E,A)` is taken, except possibly the single value `w_* = 1-E`"):
`D(1+E, A) \ {w_*} ⊆ P(𝔻)`. -/
theorem eq_punctured (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1)
    (hjA : ‖P.coeff j‖ = coefMax n P) :
    Metric.ball (1 + P.coeff (n - j) / conj (P.coeff j)) (coefMax n P) \
      {1 - P.coeff (n - j) / conj (P.coeff j)} ⊆ discImage P :=
  eq_punctured_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hmir h0 hn1 hA j hj1 hjn hjA

/-- Theorem 4.1, Case 2, P025_body.tex:380-384; idea P025_body.tex:144-146: if `w_* = 1 - E` is omitted, then
`S = P - w_*` has degree `n`, constant term `E`, leading coefficient 1, all zeros on the unit circle, `A(S) = A`,
and `P(𝔻) = S(𝔻) + w_*`. -/
theorem thm_4_1_wstar (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1)
    (hjA : ‖P.coeff j‖ = coefMax n P)
    (hw : 1 - P.coeff (n - j) / conj (P.coeff j) ∉ discImage P) :
    (P - C (1 - P.coeff (n - j) / conj (P.coeff j))).natDegree = n ∧
    (P - C (1 - P.coeff (n - j) / conj (P.coeff j))).coeff 0 = P.coeff (n - j) / conj (P.coeff j) ∧
    (P - C (1 - P.coeff (n - j) / conj (P.coeff j))).coeff n = 1 ∧
    ZerosOnCircle (P - C (1 - P.coeff (n - j) / conj (P.coeff j))) ∧
    coefMaxDeg (P - C (1 - P.coeff (n - j) / conj (P.coeff j))) = coefMax n P ∧
    discImage P = (fun w => w + (1 - P.coeff (n - j) / conj (P.coeff j))) ''
      discImage (P - C (1 - P.coeff (n - j) / conj (P.coeff j))) :=
  thm_4_1_wstar_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hmir h0 hn1 hA j hj1 hjn hjA hw

/-- Remark 4.2, P025_body.tex:388-389: `|w_* - (1+E)| = 2`, so `w_*` lies in `D(1+E, A)` only when `A > 2`. -/
theorem rem_4_2_dist (E : ℂ) (hE : ‖E‖ = 1) (A : ℝ) :
    ‖(1 - E) - (1 + E)‖ = 2 ∧ ((1 - E) ∈ Metric.ball (1 + E) A ↔ 2 < A) := rem_4_2_dist_of E hE A

/-- Remark 4.2, P025_body.tex:388-390: Theorem 3.4 "is needed only when `A > 2|a_0|` and `w_*` is omitted" —
(i) without any cited input, Theorem 4.1 holds when `a_0 = 0` or `A ≤ 2|a_0|`. -/
theorem rem_4_2_no_coef (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree)
    (hmir : Mirror n P) (hsmall : P.coeff 0 = 0 ∨ coefMax n P ≤ 2 * ‖P.coeff 0‖) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P :=
  rem_4_2_no_coef_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hnc hmir hsmall

/-- Remark 4.2, P025_body.tex:380, 389-390 — (ii) without any cited input, when `w_*` is taken (normalized `P`):
"otherwise (eq:punctured) already gives `D(1+E,A) ⊂ P(𝔻)`". -/
theorem rem_4_2_wstar_taken (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hmir : Mirror n P)
    (h0 : P.coeff 0 = 1) (hn1 : P.coeff n = 1) (hA : 1 < coefMax n P) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1)
    (hjA : ‖P.coeff j‖ = coefMax n P)
    (hw : 1 - P.coeff (n - j) / conj (P.coeff j) ∈ discImage P) :
    Metric.ball (1 + P.coeff (n - j) / conj (P.coeff j)) (coefMax n P) ⊆ discImage P :=
  rem_4_2_wstar_taken_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) n hn P hdeg hmir h0 hn1 hA j hj1 hjn
    hjA hw

/-- Remark 4.2, P025_body.tex:391-392: "if `A` is attained at some index `j ≠ n/2`, then `A(S) = |a_j|` with
`j ≠ n/2`, and [OR74, Theorem 3] or [SS74, Theorem 3] suffices": Theorem 4.1 follows from the coefficient bound for
`k ≠ n/2` alone (hypothesis `hOR`, the statement of [OR74, Thm 3] and [SS74, Thm 3] for `k ≠ n/2`). -/
theorem rem_4_2_off_middle
    (hOR : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q →
      ∀ k ≤ Q.natDegree, 2 * k ≠ Q.natDegree → ‖Q.coeff k‖ ≤ maxMod Q / 2)
    (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree) (hmir : Mirror n P)
    (hj : ∃ j ≤ n, 2 * j ≠ n ∧ ‖P.coeff j‖ = coefMax n P) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P :=
  rem_4_2_off_middle_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) thm_3_1 hOR n hn P hdeg hnc hmir hj

/-- Support for Remark 4.2, P025_body.tex:392-393: the middle case is not needed unless `n` is even and `|a_{n/2}|` is
strictly larger than every other `|a_k|` (the first two of the four conditions of `rem_4_2_middle_used_only`). -/
theorem rem_4_2_middle_only
    (hOR : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q →
      ∀ k ≤ Q.natDegree, 2 * k ≠ Q.natDegree → ‖Q.coeff k‖ ≤ maxMod Q / 2)
    (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree) (hmir : Mirror n P)
    (hnot : ¬ (Even n ∧ ∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖)) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P :=
  rem_4_2_middle_only_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) thm_3_1 hOR n hn P hdeg hnc hmir hnot

/-- Remark 4.2, P025_body.tex:392-393 (coverage link): "the middle case of Theorem 3.4, due to Kristiansen, is used
only when `n` is even, `|a_{n/2}|` is strictly larger than every other `|a_k|` and than `2|a_0|`, and `w_*` is
omitted": unless all four hold, Theorem 4.1 follows from the bound for `k ≠ n/2` alone (hypothesis `hOR`). `w_*` is
`1 - E` for the normalized `Q = P(αz)/a_0` and `j = n/2`; "`w_*` is omitted" is stated for every admissible `α` (with
`a_0 ≠ 0`: Case 1 has no `w_*`). -/
theorem rem_4_2_middle_used_only
    (hOR : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q →
      ∀ k ≤ Q.natDegree, 2 * k ≠ Q.natDegree → ‖Q.coeff k‖ ≤ maxMod Q / 2)
    (n : ℕ) (hn : 1 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (hnc : 0 < P.natDegree) (hmir : Mirror n P)
    (hnot : ¬ (Even n ∧ (∀ k ≤ n, k ≠ n / 2 → ‖P.coeff k‖ < ‖P.coeff (n / 2)‖) ∧
      2 * ‖P.coeff 0‖ < ‖P.coeff (n / 2)‖ ∧ P.coeff 0 ≠ 0 ∧
      ∀ alpha : ℂ, ‖alpha‖ = 1 → alpha ^ n = P.coeff 0 / P.coeff n →
        1 - (normalizeAt P alpha).coeff (n - n / 2) / conj ((normalizeAt P alpha).coeff (n / 2)) ∉
          discImage (normalizeAt P alpha))) :
    ∃ c : ℂ, Metric.ball c (coefMax n P) ⊆ discImage P :=
  rem_4_2_middle_used_only_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) thm_3_1 hOR n hn P hdeg hnc hmir hnot

/-- Remark 4.2, P025_body.tex:393-395: "The middle case cannot be bypassed: by Theorem 3.1, for polynomials with all
zeros on the unit circle Theorem 4.1 is equivalent to Theorem 3.4": the covering statement is equivalent to the
coefficient bound, and, given the cases `k ≠ n/2`, to the middle case. -/
theorem rem_4_2_equiv (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ZerosOnCircle P) :
    ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔
      ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2) ∧
    ((∀ k ≤ P.natDegree, 2 * k ≠ P.natDegree → ‖P.coeff k‖ ≤ maxMod P / 2) →
      ((∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P) ↔
        ∀ k : ℕ, 2 * k = P.natDegree → ‖P.coeff k‖ ≤ maxMod P / 2)) := rem_4_2_equiv_of thm_3_1 P hdeg hz

/-! ## Section 5 and Figure 2 -/

/-- Example 5.1, P025_body.tex:433-436 and P025_body.tex:110-111; Figure 1's caption, P025_body.tex:102 ("`A` is the best
radius that holds for all of them"). -/
theorem ex_5_1 (n : ℕ) (hn : 1 ≤ n) :
    Mirror n (polyOnePlusPow n) ∧ (polyOnePlusPow n).natDegree = n ∧ coefMaxDeg (polyOnePlusPow n) = 1 ∧
    discImage (polyOnePlusPow n) = Metric.ball 1 1 ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage (polyOnePlusPow n) → r ≤ 1) ∧
    (∀ c : ℂ, ¬ Metric.closedBall c 1 ⊆ discImage (polyOnePlusPow n)) := ex_5_1_proved n hn

/-- Example 5.2, P025_body.tex:440-451 ("here `E = 1`, and `w_* = 0` is taken because `P(z) = 0` when `z^m` is the root
of `t^2+at+1` in `(-1,0)` ..., so the disc of the proof is `D(2,a)`", P025_body.tex:448-450); with Example 5.1, Figure 1's caption, P025_body.tex:102. -/
theorem ex_5_2 (a : ℝ) (ha : 4 ≤ a) (m : ℕ) (hm : 1 ≤ m) :
    (∀ z : ℂ, ∀ θ : ℝ, z ^ m = Complex.exp (θ * Complex.I) →
      (polyLimacon a m).eval z = Complex.exp (θ * Complex.I) * ((a : ℂ) + 2 * Real.cos θ) ∧
      ((polyLimacon a m).eval z).re = a * Real.cos θ + 2 * Real.cos θ ^ 2) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt (fun y : ℝ => a * y + 2 * y ^ 2) (a + 4 * x) x ∧ 0 ≤ a + 4 * x ∧
      2 - a ≤ a * x + 2 * x ^ 2 ∧ a * x + 2 * x ^ 2 ≤ 2 + a) ∧
    (∀ w ∈ discImage (polyLimacon a m), 2 - a < w.re ∧ w.re < 2 + a) ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage (polyLimacon a m) → r ≤ a) ∧
    (polyLimacon a m).natDegree = 2 * m ∧ Mirror (2 * m) (polyLimacon a m) ∧
    coefMaxDeg (polyLimacon a m) = a ∧
    (polyLimacon a m).coeff (2 * m - m) / conj ((polyLimacon a m).coeff m) = 1 ∧
    Metric.ball 2 a ⊆ discImage (polyLimacon a m) ∧
    (∃ z ∈ unitDisc, (polyLimacon a m).eval z = 0) :=
  ex_5_2_of (fun m H hd hD => (lem_2_2_b m H hd hD).2.2) a ha m hm

/-- Figure 2, left (caption P025_body.tex:426-428; label P025_body.tex:412): `(1+z)^2` maps the circle onto the cardioid
`ρ = 2 + 2 cos ψ`; `P(𝔻)` is the region it bounds (`0 < ρ < 2 + 2 cos ψ`, `w = ρ e^{iψ}`); all zeros on the circle;
`M = 4`, `A = 2`; the largest disc inside is `D(2,2)` (radius `M/2 = A`, and no other disc of radius 2 lies inside). -/
theorem fig2_cardioid :
    (∀ ψ : ℝ, polyCardioid.eval (Complex.exp (ψ * Complex.I)) =
      ((2 + 2 * Real.cos ψ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) ∧
    discImage polyCardioid = {w : ℂ | w ≠ 0 ∧ ‖w‖ < 2 + 2 * Real.cos (Complex.arg w)} ∧
    ZerosOnCircle polyCardioid ∧ maxMod polyCardioid = 4 ∧ coefMaxDeg polyCardioid = 2 ∧
    Metric.ball 2 2 ⊆ discImage polyCardioid ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage polyCardioid → r ≤ 2 ∧ (r = 2 → c = 2)) :=
  fig2_cardioid_proved

/-- Figure 2, right (caption P025_body.tex:428-430; label P025_body.tex:424; picture P025_body.tex:415-425):
`1 + 4z + z^2` maps the circle onto the limaçon `ρ = 4 + 2 cos ψ`; `P(𝔻)` is the region it bounds (`ρ < 4 + 2 cos ψ`);
it lies in the strip `-2 < Re w < 6`; the disc `D(2,4)` lies in it and has the largest possible radius `A = 4`; and
"the grey disc is `D(3,3)`, of radius `M/2`" (P025_body.tex:430): `M = 6` and `D(3,3) ⊆ P(𝔻)`. -/
theorem fig2_limacon :
    (∀ ψ : ℝ, polyFour.eval (Complex.exp (ψ * Complex.I)) =
      ((4 + 2 * Real.cos ψ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) ∧
    discImage polyFour = {w : ℂ | ‖w‖ < 4 + 2 * Real.cos (Complex.arg w)} ∧
    (∀ w ∈ discImage polyFour, -2 < w.re ∧ w.re < 6) ∧
    coefMaxDeg polyFour = 4 ∧ Metric.ball 2 4 ⊆ discImage polyFour ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage polyFour → r ≤ 4) ∧
    maxMod polyFour = 6 ∧ Metric.ball 3 3 ⊆ discImage polyFour := fig2_limacon_full_proved

/-! ## The abstract and the introduction: rows proved from Theorem 3.1 and Theorem 4.1 (placed last for Lean's order) -/

/-- Abstract P025_body.tex:13-15, Table P025_body.tex:69-70, P025_body.tex:86-87: Sheil-Small's question has the answer
yes: every self-inversive `P` maps `𝔻` onto a domain containing an open disc of radius `A`. -/
theorem abs_self_inversive (P : ℂ[X]) (hP : SelfInversive P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P := abs_self_inversive_of thm_4_1 P hP

/-- Abstract P025_body.tex:16-17 ("the self-inversive polynomials, whose zeros are symmetric with respect to the unit
circle"), P025_body.tex:46-47 and 109-110 (Sheil-Small's own reading, zeros symmetric under `ζ ↦ 1/ζ̄`): such a `P`
(degree `≥ 1`, `P(0) ≠ 0`) has an open disc of radius `A` in `P(𝔻)`. -/
theorem abs_zeros_conj_inv (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (h0 : P.eval 0 ≠ 0) (hsym : ZerosSymmConjInv P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P := abs_zeros_conj_inv_of thm_4_1 P hdeg h0 hsym

/-- Abstract P025_body.tex:17-19 ("the polynomials whose zeros, with multiplicity, are symmetric under taking reciprocals
(the literal reading of the problem as printed)"), P025_body.tex:106-110, the problem as printed P025_body.tex:55-57
(zeros symmetric under `ζ ↦ 1/ζ`). -/
theorem abs_zeros_inv (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (h0 : P.eval 0 ≠ 0) (hsym : ZerosSymmInv P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P := abs_zeros_inv_of thm_4_1 P hdeg h0 hsym

/-- P025_body.tex:107 (the literal reading in coefficient form, `a_{n-k} = ±a_k`, non-constant; Figure 1's caption,
P025_body.tex:98). -/
theorem abs_plus_minus (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hP : PlusMinusPalindromic P.natDegree P) :
    ∃ c : ℂ, Metric.ball c (coefMaxDeg P) ⊆ discImage P := abs_plus_minus_of thm_4_1 P hdeg hP

/-- P025_body.tex:127-129: "By Theorem 3.1, a positive answer for self-inversive polynomials also implies the inequality
`M ≥ 2A` of O'Hara-Rodriguez, Saff-Sheil-Small and Kristiansen for polynomials with all zeros on the unit circle, so any
proof of this answer also proves that inequality":
the covering statement for the polynomials with all zeros on the circle (a subclass of the self-inversive ones, so this
row assumes less) implies that inequality, in the form of Theorem 3.4. -/
theorem intro_covering_implies_coef
    (hcov : ∀ Q : ℂ[X], 1 ≤ Q.natDegree → ZerosOnCircle Q → ∃ c : ℂ, Metric.ball c (coefMaxDeg Q) ⊆ discImage Q) :
    ∀ P : ℂ[X], 1 ≤ P.natDegree → ZerosOnCircle P → ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ maxMod P / 2 :=
  intro_covering_implies_coef_of thm_3_1 hcov

/-- Figure 1 (caption P025_body.tex:96-97; the figure's words "as here", "with largest coefficient `A=5`", "disc of radius
`A`" and "`A=5`" on the radius): `1 + z + 5z^2 + z^3 + z^4` is self-inversive, `A = 5`, its zeros lie off the unit circle,
and `P(𝔻)` contains an open disc of radius 5 (Theorem 4.1). -/
theorem fig1_example :
    SelfInversive polyFive ∧ coefMaxDeg polyFive = 5 ∧ (∀ z : ℂ, polyFive.IsRoot z → ‖z‖ ≠ 1) ∧
      ∃ c : ℂ, Metric.ball c 5 ⊆ discImage polyFive := fig1_example_of thm_4_1

/-! ## NOT stated
-/

end Sheil.Paper
