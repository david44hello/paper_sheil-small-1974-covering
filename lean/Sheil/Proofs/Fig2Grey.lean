/- Sheil/Proofs/Fig2Grey.lean — proofs of the rows fig2_grey_disc, fig2_limacon_full of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Sheil.Proofs.ExSmall
import Sheil.Proofs.ExLimacon
import Sheil.Proofs.MaxPoint

namespace Sheil

open Polynomial

/-- `M(1 + 4z + z^2) = 6`, and the disc `D(P(1)/2, M/2) = D(3,3)` of Proposition 3.3 lies in `P(𝔻)`. -/
theorem fig2_grey_disc_proved :
    maxMod polyFour = 6 ∧ Metric.ball 3 3 ⊆ discImage polyFour := by
  obtain ⟨hself, hM2, -⟩ := intro_ex_four_proved
  have hM : maxMod polyFour = 6 := by linarith
  obtain ⟨h1, lam, hlam, hst⟩ := hself
  have hev : polyFour.eval 1 = 6 := by norm_num [polyFour]
  have hnorm : ‖polyFour.eval 1‖ = maxMod polyFour := by
    rw [hev, hM]
    norm_num
  have hball := (Proofs.prop_3_3_proved polyFour.natDegree polyFour le_rfl (by omega) lam hlam hst 1
    (by simp) hnorm).2.2
  rw [hev, hM] at hball
  refine ⟨hM, ?_⟩
  convert hball using 2 <;> norm_num

/-- Row `fig2_limacon` (Figure 2, right): the limaçon facts of ExLimacon.lean and the grey disc. -/
theorem fig2_limacon_full_proved :
    (∀ ψ : ℝ, polyFour.eval (Complex.exp (ψ * Complex.I)) =
      ((4 + 2 * Real.cos ψ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) ∧
    discImage polyFour = {w : ℂ | ‖w‖ < 4 + 2 * Real.cos (Complex.arg w)} ∧
    (∀ w ∈ discImage polyFour, -2 < w.re ∧ w.re < 6) ∧
    coefMaxDeg polyFour = 4 ∧ Metric.ball 2 4 ⊆ discImage polyFour ∧
    (∀ c : ℂ, ∀ r : ℝ, Metric.ball c r ⊆ discImage polyFour → r ≤ 4) ∧
    maxMod polyFour = 6 ∧ Metric.ball 3 3 ⊆ discImage polyFour := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := fig2_limacon_proved
  exact ⟨h1, h2, h3, h4, h5, h6, fig2_grey_disc_proved⟩

#print axioms fig2_limacon_full_proved

end Sheil
