import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcFieldIntegrality
import GaloisForLFunctions.HTGeometry.ValuationCriticalFibreLift

/-!
# Integral lift of geometric sheets at the normal-closure arc place

Every actual geometric sheet is integral at the chosen extension of the common-scale place.  The
low coefficient blocks therefore descend from the normal-closure critical fibre to the critical
fibre over the chosen discrete valuation ring.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

/-- Every actual geometric sheet has an integral representative in the critical fibre of the
chosen arc DVR. -/
noncomputable def criticalGeometricSheetToArcFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n →
      criticalFibre (ArcValuationRing K m n hm hn) m n
        (criticalNormalClosureArcRawTail K hm hn)
        (criticalNormalClosureArcReciprocalTail K hm hn) := by
  intro σ
  let p := criticalGeometricSheetToArcFieldFibre K hm hn σ
  let hmem := criticalNormalClosureArcFieldFibre_coefficients_mem K hm hn p
  exact valuationSubringCriticalFibreLift
    (ArcValuationRing K m n hm hn)
    (criticalNormalClosureArcRawTail K hm hn)
    (criticalNormalClosureArcReciprocalTail K hm hn) p hmem

end

end GaloisForLFunctions.HTGeometry
