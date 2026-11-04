/- Sheil/Cited/CoefHalfMax.lean — the ONE cited result of the paper (Theorem 3.4), stated with Mathlib terms only, with
its sources. Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Mathlib

namespace Sheil.Cited

open Polynomial

/-- Theorem 3.4 of the paper (P025_body.tex:308-311 of the FINAL text v2.30, md5 1538df2f): if `P(z) = Σ_{k=0}^n a_k z^k` has degree
`n ≥ 1` and all its zeros on the unit circle, then `|a_k| ≤ M(P)/2` for `0 ≤ k ≤ n`, `M(P) = max_{|z|=1} |P(z)|`.
Stated with Mathlib terms only (no project definition), so that no later edit of `Sheil.Defs` can change it.

Sources (journal articles, refereed):
(1) P. J. O'Hara and R. S. Rodriguez, Some properties of self-inversive polynomials, Proc. Amer. Math. Soc. 44 (1974),
331-335, Theorem 3 (p. 333): "If P has all its zeros on |z|=1 and P(z) = Σ_{j=0}^n a_j z^j, a_n ≠ 0, then
2|a_j| ≤ ||P|| for each j ≠ n/2 and 2^{1/2}|a_{n/2}| ≤ ||P||." (||F|| = max modulus of F on the unit circle, p. 332.)
Read in full.
(2) E. B. Saff and T. Sheil-Small, Coefficient and integral mean estimates for algebraic and trigonometric polynomials
with restricted zeros, J. London Math. Soc. (2) 9 (1974), 16-22, Theorem 3: "Let the polynomial P(z) = Σ_0^n a_k z^k
be as in Theorem 1. Then |a_k| ≤ M/2, for k = 0, 1, ..., n, k ≠ n/2." (Theorem 1: a "polynomial of degree n having all
its zeros on the unit circle", "M = max_{|z|=1} |P(z)|".) Read in full, in the authors'
galley (7 pages; its page numbers are not the journal's).
(3) The middle case k = n/2 (n even): G. K. Kristiansen, Some inequalities for algebraic and trigonometric polynomials,
J. London Math. Soc. (2) 20 (1979), 300-314, with the correction (2) 22 (1980), 575-576. Kristiansen's proof was NOT
read (paywalled). Stated by: Q. I. Rahman and G. Schmeisser, Analytic Theory of Polynomials, Oxford 2002,
preface p. viii (the preface was read; the account itself was not): "G. Kristiansen's proof of the fact that the
modulus of the middle coefficient of a polynomial f of even degree, having all its zeros on the unit circle, does not
exceed M/2, where M is the maximum modulus of f on the unit circle."; and W. K. Hayman and E. F. Lingham, Research
Problems in Function Theory, Springer 2019, Update 4.2: "Kristiansen [497] has proved that M ≥ 2A in general."

Lean: degree `n = natDegree P ≥ 1` (so `a_n ≠ 0`; for `n = 0` the statement is false and is excluded), every zero `z`
of `P` has `‖z‖ = 1`, and `M` = the supremum of `‖P z‖` over the unit circle (a compact set, so the maximum). -/
axiom coef_half_max (P : ℂ[X]) (hdeg : 1 ≤ P.natDegree) (hz : ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1) :
    ∀ k ≤ P.natDegree, ‖P.coeff k‖ ≤ sSup ((fun z => ‖P.eval z‖) '' Metric.sphere (0 : ℂ) 1) / 2

end Sheil.Cited
