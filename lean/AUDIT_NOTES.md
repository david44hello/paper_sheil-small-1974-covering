# AUDIT_NOTES — project 025 Lean (Sheil-Small's (1974) covering problem has a positive answer): modelling and route notes

Every row of `Sheil/Paper/Statements.lean` is one printed claim (or one part of a claim), named by the paper's numbering;
its docstring gives the paper lines. `AUDIT.md` (made by `scripts/audit.py`) lists each row's axioms; `CLAIM_MAP.tsv`
maps every printed claim to its rows (`scripts/census.py` prints the census). This file records what a reader must know
to judge that the Lean statements say what the paper says. Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now.

## 0. STATUS
- Rows: every row of Statements has a proof term. Each row depends only on Lean's three standard axioms (propext,
  Classical.choice, Quot.sound), plus, in the rows that use Theorem 3.4, the ONE cited input `Sheil.Cited.coef_half_max`.
  Counts, census and the kernel replay: section G.
- The abstract's Lean sentence ("The main theorem is also proved in the Lean 4 proof assistant, with the coefficient
  bound of O'Hara-Rodriguez, Saff-Sheil-Small and Kristiansen taken as given") is an AUDIT CHECK, not a census claim:
  row `thm_4_1` is PROVED-FROM-CITED and its only non-standard input is `Sheil.Cited.coef_half_max`.

## A. Definitions (Sheil/Defs/Basic.lean, Sheil/Defs/Examples.lean — the trust surface)
- `unitDisc` = the open ball of radius 1; `discImage P` = `P(𝔻)`; discs `D(c,r)` are `Metric.ball c r` (open), as the
  paper defines them; in particular Theorem 3.1's discs are open.
- `pstar n H` = `Σ_{k≤n} conj(h_{n-k}) z^k`, the paper's `H*` for `deg H ≤ n` (padded; `h_n` may vanish). Row
  `pstar_eval` proves the paper's formula `z^n conj H(1/z̄)` at `z ≠ 0`.
- `coefMax n P` = `max_{k≤n} |a_k|` (the `A` of Theorem 4.1, degree at most `n`); `coefMaxDeg P` = the same with
  `n = deg P` (the `A(P)` of Section 1). `maxMod P` = the supremum of `|P|` on the unit circle; row `exists_max_circle`
  proves that it is attained (the paper's max).
- `SelfInversive P` = `deg P ≥ 1` and `P* = λP` for some `|λ| = 1`, with `n = deg P` (Section 1's definition).
  `ZerosOnCircle P` = every zero has modulus 1 (false for `P = 0`). `Mirror n P` = (eq:mirror).
  `PlusMinusPalindromic n P` = `a_{n-k} = ε a_k` with ONE `ε ∈ {1, -1}` for all `k` (as in Lemma 2.1(b)).
  `ZerosSymmConjInv`, `ZerosSymmInv` = zero symmetry WITH multiplicities (`rootMultiplicity`); rows using them assume
  `P(0) ≠ 0`, as the paper does.
- `schurCohn n H` = the explicit entry formula of the recursion in Lemma 2.2(c)'s proof; row `schurCohn_unique` proves
  it IS the coefficient matrix of `K(z,η)` (so no choice is hidden in the definition). `normalizeAt P α` = `P(αz)/a_0`.
- `trigT c m P θ` = `c e^{-imθ} P(e^{iθ})` for complex `θ` (the note after Theorem 3.4): `trigT 1` is the paper's `Q`,
  `trigT c` its `T = cQ`.
- Examples: `polyThreeI`, `polyFour`, `polyOnePlusPow n`, `polyLimacon a m`, `polyCardioid` are the printed
  polynomials; the four Figure 1 witnesses (`polyOnePlusSq`, `polyXSubI`, `polySelfInvOnly`, `polyMirrorOnly`) show
  that every region the figure draws is non-empty (row `fig1_regions`).

## B. The ONE cited input (Sheil/Cited/CoefHalfMax.lean; scripts/cited_inputs.json)
- `Sheil.Cited.coef_half_max` = Theorem 3.4 exactly: `deg P = n ≥ 1`, all zeros on the unit circle, then
  `|a_k| ≤ M(P)/2` for `0 ≤ k ≤ n`. Stated with Mathlib terms only (no project definition can change it).
- Sources, all refereed journal articles: O'Hara-Rodriguez 1974 Theorem 3 and Saff-Sheil-Small 1974 Theorem 3 (`k ≠ n/2`;
  O'Hara-Rodriguez read in full, Saff-Sheil-Small read in full in the authors' galley; both quoted verbatim in the
  docstring); Kristiansen 1979 with the 1980 correction (the middle case `k = n/2`; the 1979 proof NOT read,
  paywalled; the 1980 correction was read: the statement rests on Rahman-Schmeisser 2002, preface p. viii, and
  Hayman-Lingham 2019, Update 4.2, both quoted). Status: refereed. The Lean text was checked against the sources
  before use, and again by an independent reviewer.
- Layout: no proof file imports `Cited/`; the cited bound enters proofs as the hypothesis type
  `HypCoef` (Sheil/Proofs/Rows.lean), and only `Statements.lean` applies the cited input (row `cor_3_5`).
- Rows whose CONCLUSION is (part of) Theorem 3.4 are proved WITHOUT the cited input (else they would be empty):
  `intro_covering_implies_coef`, `rem_4_2_equiv`; the Remark 4.2 rows `rem_4_2_off_middle`, `rem_4_2_middle_only`,
  `rem_4_2_middle_used_only` assume only `hOR` = the published bound for `k ≠ n/2` ([OR74, Thm 3] = [SS74, Thm 3]) as an
  explicit hypothesis, which is what the remark claims.

## C. Route differences (the Lean proof differs from the paper's proof; the statement does not)
- Assembly: rows that rest on other rows take them as explicit hypotheses (`Hyp31` = Theorem 3.1, `HypPSD` = the PSD
  half of Lemma 2.2(b), `HypThm41` = Theorem 4.1, `HypCoef` = Theorem 3.4); Statements instantiates them with the rows.
- Lemma 2.1 (Sheil/Proofs/Lemma21.lean): through the multiset of roots — `P*` has the roots `1/ζ̄`, the reversal the
  roots `1/ζ` (when `P(0) ≠ 0`), and two polynomials of the same degree with the same roots are proportional.
- Lemma 2.2(b) (GramExpansion.lean, GramPSD.lean, SchurIdentity.lean): the paper's Gram expansion
  `K = |h_0|^2 Σ_l (1-|β_l|^2) f_l(z) conj f_l(η)` is proved by induction on `n` instead of the telescoping sum; the
  coefficient matrix is identified by comparing the two double sums (row `schurCohn_unique`).
- Proposition 3.3 (MaxPoint.lean): the paper differentiates `log |F(e^{it})|^2`; Lean uses that `t ↦ |F(ζe^{it})|^2`
  is stationary at its maximum `t = 0` (so `ζF'(ζ) conj F(ζ)` is real) and the reversal identity for `F* = λF` at `ζ`;
  together they give `ζF'(ζ) = (n/2) F(ζ)`. Same hypotheses, same conclusion.
- Theorem 3.1's last step (`|c| + r ≤ M`, `|c| ≥ r`, so `2r ≤ M`) follows the paper.
- Theorem 4.1 follows the paper's two cases, the normalization, the constant diagonal, the `2×2` minor, (eq:punctured)
  and the polynomial `S = P - w_*`; the circle case is Corollary 3.5 (Theorem 3.1 with the cited Theorem 3.4).

## D. Formalization choices for running text (CLAIM_MAP.tsv has every claim)
- The abstract's classes are stated at `n = deg P`: rows `abs_self_inversive`, `abs_zeros_conj_inv`, `abs_zeros_inv`,
  `abs_plus_minus` (Theorem 4.1 with `n = deg P`); "a domain" = open and connected (row `abs_domain`).
- The note after Theorem 3.4 (row `coef_note_trig`): "its 2m zeros in a period are all real" is stated through the zeros
  of `P` — `P` has `2m` zeros with multiplicity, `T(θ) = 0` iff `P(e^{iθ}) = 0` (complex `θ`), every zero of `T` is real,
  and `t ↦ e^{it}` maps the zeros of `T` in `[0, 2π)` one-to-one onto the zeros of `P`. The zeros of a trigonometric
  polynomial of degree `m` are, by definition, those of the algebraic polynomial `z^m T`, here `c P(z)`; multiplicities
  of an entire function of `θ` would add nothing the note uses. `max |T|` is stated as the supremum (attained).
- Example 5.2's "`w_* = 0` is taken because `P(z) = 0` when `z^m` is the root of `t^2+at+1` in `(-1,0)`" is the row's
  clause "P has a zero in 𝔻".
- Lemma 3.2's relation to de Bruijn's theorem is attribution (NOT COUNTED); row `lem_3_2_closed` (the closed-region
  case) is a support row of the claim L32.
- Coverage links (a running-text claim one step from a row gets its own row): `lem_2_2_a_pstar` (the remark
  before Lemma 2.2), `sketch_disc_one` (the sketch's `D(1,1) ⊂ P(𝔻)` for every `A`), `rem_4_2_middle_used_only`
  (Remark 4.2's four conditions for the middle case).
- The quantifier rule: every printed quantifier and exception was compared with the row's type;
  a row that is true WITH an exception does not cover a sentence WITHOUT it.

## E. The paper's text
- Every `P025_body.tex:<line>` pointer and every quote names a line of the paper's TeX source as published (tag v2.30,
  `P025_body.tex` md5 1538df2f5460d3b01212901be2ed10d5). Each pointer was checked against that file.
- Exceptions are kept exactly: the minor gives `|w-(1+E)| ≥ A` only "unless `w = 1-E`" (row `eq_punctured`: the
  punctured disc `D(1+E,A) \ {1-E}` lies in `P(𝔻)`); no row drops an exception that the text states.
- Claim I4 of the census ("polynomials whose zeros all lie on the unit circle are the basic examples") is not in the
  published text; its row `lem_2_1_circle` remains and covers L21d.

## F. Tree hygiene
- `./check.sh` (README) runs `scripts/check.sh --final`: build, banned words (`sorry`, `admit`, `native_decide`, ... and
  `axiom` outside Cited/), the audit, the final gate. Lean runs with one thread.
- Not part of the published folder: backups, logs, `scripts/audit_output.log` (rewritten on every audit run), `.lake/`.

## G. Counts and kernel replay
- Rows (`AUDIT.md`): 54 rows in `Sheil/Paper/Statements.lean` = 47 PROVED + 6 PROVED-FROM-CITED + 1 CITED + 0 OPEN.
  The CITED row is `thm_3_4` (Theorem 3.4 itself); the 6 PROVED-FROM-CITED rows are `cor_3_5`, `thm_4_1`,
  `abs_self_inversive`, `abs_zeros_conj_inv`, `abs_zeros_inv`, `abs_plus_minus`. Every other row's `#print axioms`
  lists only propext, Classical.choice and Quot.sound.
- Census (`CLAIM_MAP.tsv`, `scripts/census.py`): 52 printed claims = 44 PROVED + 7 PROVED-FROM-CITED + 1 CITED
  (T34 = Theorem 3.4) + 0 OPEN.
- Kernel replay of this code (Lean 4 v4.35.0, Mathlib v4.35.0), one thread:
  - leanchecker, olean replay: all 23 modules that declare constants, PASS.
  - Export of every safe `Sheil` constant with its dependencies (555 constants, 56,563 declaration records), checked
    from an empty environment: leanchecker PASS, leanchecker-paranoid PASS, lean4lean PASS (56,560 declarations),
    nanoda PASS (59,310 declarations). con-leche and con-ron decline any export that contains a non-standard axiom
    (here `Sheil.Cited.coef_half_max`), so they did not run.
  - Axioms in the export: propext, Quot.sound, Classical.choice, `Sheil.Cited.coef_half_max`.
