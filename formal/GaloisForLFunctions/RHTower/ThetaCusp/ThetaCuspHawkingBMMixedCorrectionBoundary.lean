import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMInhomogeneousCorrectionBoundary

set_option autoImplicit false

/-!
# Complete mixed correction work and its original boundary exchange

The actual mixed nonlinear source derivative retains both quadratic correction
discrepancies and the cubic discrepancy. Each quadratic work term is exchanged
against the independent full test, preserving its Einstein residual and the
original differentiated boundary divergence. Every scalar/vector amplitude,
tensor component and original metric weight remains in the identity.
-/

namespace RHTower.D4BMMixedCorrectionBoundary
open GaloisForLFunctions.HTGeometry ComplexCoordinateMetricTwoJet
open D4BMBackground D4BMWeightedCorrectionDiscrepancy D4BMInhomogeneousCorrectionBoundary
noncomputable section
local notation "Space" => ComplexMetricTwoJetSpace 4
local notation "Jet" => CoordinateMetricTwoJet 4 ℂ

/-- Exact complete mixed-source exchange before causal integration, with both independent correction channels. -/
theorem complete_mixed_exchange (p : ExteriorPoint) (q : Fin 2 → XiZeroCopy)
    (b : Fin 2 → Bool) (aS aV : Fin 2 → ℂ) (K L B : Fin 4 → Space)
    (A : Fin 4 → Jet) (M : Jet) :
    mixedDiscrepancy p q b aS aV K L (fun i => toSpace (symmetricCorrection (A i))) B
      (symmetricCorrection M).metric=
      linearWork p (B 1) (symmetricCorrection M).metric+
      (exchangedSourceWork p (q 0) (b 0) (aS 0) (aV 0) (symmetricCorrection (A 1)) (symmetricCorrection M)+
        testResidualWork p (q 0) (b 0) (aS 0) (aV 0) (symmetricCorrection (A 1)) (symmetricCorrection M)+
        boundaryDefect p (q 0) (b 0) (aS 0) (aV 0) (symmetricCorrection (A 1)) (symmetricCorrection M))+
      (exchangedSourceWork p (q 1) (b 1) (aS 1) (aV 1) (symmetricCorrection (A 0)) (symmetricCorrection M)+
        testResidualWork p (q 1) (b 1) (aS 1) (aV 1) (symmetricCorrection (A 0)) (symmetricCorrection M)+
        boundaryDefect p (q 1) (b 1) (aS 1) (aV 1) (symmetricCorrection (A 0)) (symmetricCorrection M)) := by
  rw [physical_mixed_discrepancy,physical_correction_exchange,physical_correction_exchange]

end
end RHTower.D4BMMixedCorrectionBoundary
