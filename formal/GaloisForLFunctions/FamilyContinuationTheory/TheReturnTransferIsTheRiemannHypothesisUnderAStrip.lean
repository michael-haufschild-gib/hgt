import GaloisForLFunctions.SignFreePurityMechanisms.HomogeneousReturnTransferImpliesStripCollapse

/-!
# The return transfer is the Riemann hypothesis under a strip

The transfer from return-free intervals of the prime orbit to bounded prime traces on log-square
windows turns every zero-free strip into the critical line
(`homogeneousReturnWindowTransfer_implies_quasiRH_collapse`). Its premise holds in every late
window as soon as a strip is known, so it selects nothing there; and its conclusion, a bound for
the prime traces, holds at every prime under the Riemann hypothesis.

* `homogeneousReturnWindowTransfer_of_riemannHypothesis`: the Riemann hypothesis gives the
  transfer, with the constant `∑_z ‖evenCoeff z‖` and no use of the premise.
* `homogeneousReturnWindowTransfer_iff_riemannHypothesis`: if the zero abscissa is below `1`,
  the transfer is equivalent to the Riemann hypothesis.

Under a zero-free half-plane the transfer is not a step from the half-plane to the line; it is
the line.
-/

open Filter Topology Complex
open Zeta23

noncomputable section

namespace GaloisForLFunctions.FamilyContinuationTheory

open GaloisForLFunctions.SignFreePurityMechanisms GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The Riemann hypothesis gives the return transfer: the prime traces are bounded at every
prime. -/
theorem homogeneousReturnWindowTransfer_of_riemannHypothesis (hRH : RiemannHypothesis) :
    HomogeneousReturnWindowTransfer := by
  intro A η δ T₁ _ _ _ _
  have hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (0 : ℝ) := by
    intro ρ hρ
    rw [riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ, add_zero]
  refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, 0, fun T _ _ p hp _ => ?_⟩
  have h := abs_two_re_lagStructure_log_le_of_width temperedConfig_zetaZeroConfig hwidth hp.pos
  simpa only [Real.rpow_zero, mul_one] using h

/-- **Under a strip the return transfer is the Riemann hypothesis.** -/
theorem homogeneousReturnWindowTransfer_iff_riemannHypothesis
    (hΘ : _root_.RHTower.zetaZeroAbscissa < 1) :
    HomogeneousReturnWindowTransfer ↔ RiemannHypothesis :=
  ⟨fun h => homogeneousReturnWindowTransfer_implies_quasiRH_collapse h hΘ,
    homogeneousReturnWindowTransfer_of_riemannHypothesis⟩

end GaloisForLFunctions.FamilyContinuationTheory
