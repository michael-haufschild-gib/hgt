import GaloisForLFunctions.RHTower.SPEQuantileRieszParabolicCovarianceHardCore
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarCovarianceExteriorProducer

/-!
# Literal SP-E landing of the exterior covariance producer

The two-moment exterior producer is not an auxiliary energy: this module lands it directly in the
unsquared completed SP-E transport.  Every displacement debt, terminal interval, physical-wall
gauge, and quadrature term remains present.  The result gives the producer's coefficient-faithful
source interface without claiming its missing cofinal cancellation bound.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- **Source-faithful exterior landing.** After multiplication by its literal positive boundary
mass, the completed SP-E source is the exterior two-moment producer, full displacement debt,
terminal interaction/form, and physical-wall gauges.  No scalarization, absolute value, or
separate estimate has removed prime--polar cancellation. -/
theorem completedSPESourceTransport_mul_boundaryMass_eq_exteriorCovariance_debt_gauges
    {M : ℕ} (hM : 3 ≤ M) :
    let K := M - 3
    let T := Real.log M
    let C := ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T
    let B := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T
    B 0 *
        (speCompletedQuantileRieszTransport M -
          (∑ n ∈ Finset.range (K + 1),
            ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) +
          2 * (Real.sqrt M - 2 / 3)) =
      2 * ccmActualHeadTwoMomentExteriorPairing
          (ccmActualHeadMatchedQuantileDisplacementMomentVector K)
          (ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector K) +
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K +
        (2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
            (ccmActualHeadQuantileParabolicTerminal K T) +
          ccmParabolicForm (ccmActualHeadQuantileParabolicTerminal K T)) +
        (Real.sqrt (M : ℝ) * B 0 - B 1) * C 1 + B 2 * C 0 := by
  dsimp only
  rw [completedSPESourceTransport_mul_boundaryMass_eq_covariance_debt_gauges hM,
    ← ccmActualHeadMatchedQuantileParabolicCovariance_eq_adjacentMatchedGapKernel,
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_eq_exteriorPairing]

end RHTower
