/- Sheil/Proofs/PstarDeriv.lean — proofs of the row lem_2_2_a_pstar of Sheil/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Sheil.Proofs.MaxPoint

namespace Sheil.Proofs

open Polynomial ComplexConjugate

lemma pstar_sub (n : ℕ) (F G : ℂ[X]) :
    pstar n (F - G) = pstar n F - pstar n G := by
  ext k
  simp only [coeff_pstar, coeff_sub]
  split_ifs <;> simp

lemma pstar_derivative_norm (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(pstar n H).derivative.eval z‖ = ‖(n : ℂ) * H.eval z - z * H.derivative.eval z‖ := by
  let G : ℂ[X] := C (n : ℂ) * H - X * H.derivative
  have hGdeg : G.natDegree ≤ n :=
    (natDegree_sub_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans hdeg) (euler_natDegree_le n H hdeg))
  have hstar : pstar n G = X * (pstar n H).derivative := by
    dsimp [G]
    rw [pstar_sub, pstar_C_mul, pstar_euler]
    simp only [map_natCast]
    ring
  have hnorm := pstar_norm_circle_proved n G hGdeg z hz
  rw [hstar, eval_mul, eval_X, norm_mul, hz, one_mul] at hnorm
  simpa [G] using hnorm

theorem lem_2_2_a_pstar_proved (n : ℕ) (H : ℂ[X]) (hdeg : H.natDegree ≤ n)
    (hD : ∀ z ∈ unitDisc, H.eval z ≠ 0) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖H.derivative.eval z‖ ≤ ‖(pstar n H).derivative.eval z‖ := by
  rw [pstar_derivative_norm n H hdeg z hz]
  have h := lem_2_2_a_proved n H hdeg hD z hz
  simpa [norm_mul, hz] using h

#print axioms lem_2_2_a_pstar_proved

end Sheil.Proofs
