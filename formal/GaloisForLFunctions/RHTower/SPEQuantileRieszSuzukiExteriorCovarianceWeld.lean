import GaloisForLFunctions.RHTower.SPEQuantileRieszExteriorCovarianceProducerLanding
import GaloisForLFunctions.RHTower.SPEQuantileRieszSuzukiEulerianBridge

/-!
# Exact exterior-covariance--Suzuki Eulerian weld

The literal SP-E and Suzuki Eulerian reporters carry one completed prime--polar charge.  This
module transports the source-faithful exterior covariance landing to the literal Suzuki
discrepancy without bounding, scalarizing, or splitting that charge.  Suzuki's bounded residual,
SP-E quadrature seam, displacement debt, terminal form, and physical-wall gauges all remain in
the equality.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- **Source-faithful exterior--Suzuki weld.** The exact completed Suzuki discrepancy, after its
literal normalization and with its polar--lattice residual retained, lands on the same nonlinear
actual-head exterior covariance as SP-E.  This is an identity of the literal signed source; it
does not assert the missing cofinal bound. -/
theorem suzukiEulerianDiscrepancy_mul_boundaryMass_eq_exteriorCovariance_debt_gauges
    {M : ℕ} (hM : 3 ≤ M) :
    let K := M - 3
    let T := Real.log M
    let C := ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T
    let B := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T
    B 0 *
        (2 * (M : ℝ) *
            (suzukiEulerianCompletedOutgoingResidual (M - 1) -
              suzukiEulerianCompletedOutgoingDiscrepancy (M - 1)) -
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
  have hN : 2 ≤ M - 1 := by omega
  have hbridge : suzukiEulerianCompletedOutgoingDiscrepancy (M - 1) =
      -speCompletedQuantileRieszTransport M / (2 * (M : ℝ)) +
        suzukiEulerianCompletedOutgoingResidual (M - 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ M)] using
      suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_speTransport_add_residual hN
  have htransport : speCompletedQuantileRieszTransport M =
      2 * (M : ℝ) *
        (suzukiEulerianCompletedOutgoingResidual (M - 1) -
          suzukiEulerianCompletedOutgoingDiscrepancy (M - 1)) := by
    have hdiv : speCompletedQuantileRieszTransport M / (2 * (M : ℝ)) =
        suzukiEulerianCompletedOutgoingResidual (M - 1) -
          suzukiEulerianCompletedOutgoingDiscrepancy (M - 1) := by
      have hbridge' : suzukiEulerianCompletedOutgoingDiscrepancy (M - 1) =
          -(speCompletedQuantileRieszTransport M / (2 * (M : ℝ))) +
            suzukiEulerianCompletedOutgoingResidual (M - 1) := by
        simpa only [neg_div] using hbridge
      linarith
    calc
      speCompletedQuantileRieszTransport M =
          2 * (M : ℝ) * (speCompletedQuantileRieszTransport M / (2 * (M : ℝ))) := by
            field_simp
      _ = _ := by rw [hdiv]
  dsimp only
  rw [← htransport]
  exact completedSPESourceTransport_mul_boundaryMass_eq_exteriorCovariance_debt_gauges hM

end RHTower
