import GaloisForLFunctions.RHTower.SPEQuantileRieszPrimePowerHistoryTransport

/-!
# Exact orientation--debt landing of the SP-E prime-power history

The prime-power-supported strict-cross history has no independent global
degree of freedom.  Its complete finite prefix is exactly the negative
all-pair displacement--centroid orientation ledger minus the nonnegative
quadratic displacement debt.  This retains the signed covariance rather than
assuming it bounded, and identifies the single quantity a cofinal SP-E/P
estimate must control.
-/

noncomputable section
open scoped BigOperators
open Finset
namespace RHTower

private theorem strictCross_zero :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal 0)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary 0) = 0 := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_orientationLedger_sub_debt]
  simp [ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum,
    ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum]

/-- The complete prime-power history is exactly one signed orientation ledger
and one nonnegative displacement debt. -/
theorem speQuantileRieszPrimePowerHistory_eq_neg_orientationLedger_sub_debt (K : ℕ) :
    ∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
      speQuantileRieszPrimePowerHistoryCurvature n =
      -ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum K -
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K := by
  calc
    _ = ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) -
        ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal 0)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary 0) :=
      (ccmActualHeadMatchedQuantileParabolicStrictCross_sub_zero_eq_primePowerHistory K).symm
    _ = ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) := by
      rw [strictCross_zero]
      ring
    _ = _ := ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_orientationLedger_sub_debt K

/-- Every prime-power history prefix, after retaining its literal signed
orientation ledger, is nonpositive by the full displacement debt. -/
theorem speQuantileRieszPrimePowerHistory_add_orientationLedger_nonpos (K : ℕ) :
    (∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
      speQuantileRieszPrimePowerHistoryCurvature n) +
      ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum K ≤ 0 := by
  rw [speQuantileRieszPrimePowerHistory_eq_neg_orientationLedger_sub_debt]
  linarith [ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum_nonneg K]

end RHTower
