/- Sheil/Defs/Examples.lean — definitions (polyThreeI, polyFour, polyOnePlusPow, polyLimacon, polyCardioid, polyFive, polyOnePlusSq, polyXSubI, ...).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Defs.Basic

namespace Sheil

open Polynomial

/-- `1 + 3iz + z^2` (P025_body.tex:108). -/
noncomputable def polyThreeI : ℂ[X] := 1 + C (3 * Complex.I) * X + X ^ 2

/-- `1 + 4z + z^2` (P025_body.tex:130, 424, 429). -/
noncomputable def polyFour : ℂ[X] := 1 + C 4 * X + X ^ 2

/-- `1 + z^n` (Example 5.1, P025_body.tex:110, 434). -/
noncomputable def polyOnePlusPow (n : ℕ) : ℂ[X] := 1 + X ^ n

/-- `1 + a z^m + z^{2m}` (Example 5.2, P025_body.tex:441). -/
noncomputable def polyLimacon (a : ℝ) (m : ℕ) : ℂ[X] := 1 + C (a : ℂ) * X ^ m + X ^ (2 * m)

/-- `(1 + z)^2` (Figure 2, P025_body.tex:412, 426). -/
noncomputable def polyCardioid : ℂ[X] := (1 + X) ^ 2

/-- `1 + z + 5z^2 + z^3 + z^4` (Figure 1, P025_body.tex:96). -/
noncomputable def polyFive : ℂ[X] := 1 + X + C 5 * X ^ 2 + X ^ 3 + X ^ 4

/-- Witness of the retired row `fig1_regions`: `1 + z^2` (in all three classes). -/
noncomputable def polyOnePlusSq : ℂ[X] := 1 + X ^ 2

/-- Witness of the retired row `fig1_regions`: `z - i` (all zeros on the circle, not `a_{n-k} = ±a_k`). -/
noncomputable def polyXSubI : ℂ[X] := X - C Complex.I

/-- Witness of the retired row `fig1_regions`: `z^2 - (5/2) i z - 1 = (z - 2i)(z - i/2)` (self-inversive only). -/
noncomputable def polySelfInvOnly : ℂ[X] := X ^ 2 - C (5 / 2 * Complex.I) * X - 1

/-- Witness of the retired row `fig1_regions`: `1 + z + i z^2` (condition (eq:mirror) only). -/
noncomputable def polyMirrorOnly : ℂ[X] := 1 + X + C Complex.I * X ^ 2

end Sheil
