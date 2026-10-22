import GaloisForLFunctions.RHTower.SPEQuantileRieszPrimePowerHistoryLedger
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicVarianceBalance

/-!
# Physical variance landing of the SP-E prime-power history

The literal prime-power-supported history is exactly the difference between
the physical matched-centroid variance and its equal-mass quantile counterpart.
This removes neither variance and asserts no sign, but identifies their
cofinal comparison as the unique remaining scalar source inequality.
-/

noncomputable section
open scoped BigOperators
open Finset
namespace RHTower

/-- The full finite SP-E prime-power history is exactly the physical
matched-versus-quantile centroid-variance defect. -/
theorem speQuantileRieszPrimePowerHistory_eq_centroidVarianceDifference (K : ℕ) :
    ∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
      speQuantileRieszPrimePowerHistoryCurvature n =
      ccmActualHeadParabolicCentroidVariance K ccmActualHeadMatchedPolarCentroid -
        ccmActualHeadParabolicCentroidVariance K ccmActualHeadQuantilePolarCentroid := by
  rw [speQuantileRieszPrimePowerHistory_eq_neg_orientationLedger_sub_debt,
    ccmActualHeadMatchedQuantileParabolicOrientationDebt_eq_centroidVarianceDifference]

end RHTower
