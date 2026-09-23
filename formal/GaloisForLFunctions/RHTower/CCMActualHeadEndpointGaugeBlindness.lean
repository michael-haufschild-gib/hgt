import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileEndpointGauge
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileTransportProducer

/-!
# Endpoint-gauge blindness of quadratic actual-head readout

On the physical aperture, the endpoint-free and completed outgoing quantile characteristics
differ by a diameter-cosine gauge.  That gauge carries the literal terminal completed-error mass
at zero clock, yet its quadratic pairing vanishes on every physical actual head.  Hence a
Gamma--Slepian quadratic lower bound alone cannot control the terminal completed error: a valid
producer must retain a non-null cross-boundary observable.

This is an exact source-level no-go, not an RH claim.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- At its physical aperture, the endpoint-free gauge's zero clock is exactly the terminal
completed-error mass after the deterministic polar threshold is removed. -/
theorem ccmActualHeadOutgoingQuantileEndpointGauge_zero_eq_completedError_sub_threshold
    (a : SuzukiPositiveAperture) :
    ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol
        (Nat.floor (Real.exp (2 * a.1)) + 1) (2 * a.1) 0 =
      criticalMellinCompletedError (2 * a.1) -
        2 * (1 - Real.exp (-(2 * a.1 / 2))) := by
  rw [ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_zero]
  exact quantileTerminalMass_eq_completedError_sub_threshold (2 * a.1)

/-- The same endpoint gauge is invisible to every quadratic physical actual-head readout.
Together with `ccmActualHeadOutgoingQuantileEndpointGauge_zero_eq_completedError_sub_threshold`,
this excludes extracting terminal completed error from this quadratic head channel alone. -/
theorem integral_ccmActualHeadOutgoingQuantileEndpointGauge_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    (∫ xi : ℝ,
      (ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi -
        ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N (2 * a.1) xi) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  dsimp only
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  let D : ℝ → ℝ := fun xi => ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2
  have hfree := integrable_ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_mul_density
    N (2 * a.1) (f : SoninL2)
  have hcompleted := integrable_ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_mul_density
    N (2 * a.1) (f : SoninL2)
  have heq := integral_ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_eq_completed
    a N f
  change (∫ xi : ℝ,
    (ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi -
      ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N (2 * a.1) xi) * D xi) = 0
  rw [show (fun xi : ℝ =>
      (ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi -
        ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N (2 * a.1) xi) * D xi) =
      fun xi : ℝ =>
        ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi * D xi -
          ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N (2 * a.1) xi * D xi by
      funext xi
      ring]
  rw [integral_sub hfree hcompleted, heq]
  ring

end RHTower
