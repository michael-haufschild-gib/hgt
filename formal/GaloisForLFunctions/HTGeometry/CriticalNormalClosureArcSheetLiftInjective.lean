import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcSheetLift

/-! # Injectivity of the integral lift of geometric sheets -/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

theorem criticalGeometricSheetToArcFieldFibre_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalGeometricSheetToArcFieldFibre K hm hn) := by
  intro σ τ hστ
  apply criticalGeometricSheetToNormalFibre_injective K m n
  apply Subtype.ext
  have hval := congrArg Subtype.val hστ
  change (criticalGeometricSheetToNormalFibre K m n σ).1 =
    (criticalGeometricSheetToNormalFibre K m n τ).1 at hval
  exact hval

theorem criticalFibreMap_criticalGeometricSheetToArcFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) :
    criticalFibreMap (ArcValuationRing K m n hm hn).subtype m n
        (criticalNormalClosureArcRawTail K hm hn)
        (criticalNormalClosureArcReciprocalTail K hm hn)
        (criticalGeometricSheetToArcFibre K hm hn σ) =
      criticalGeometricSheetToArcFieldFibre K hm hn σ := by
  exact criticalFibreMap_valuationSubringCriticalFibreLift
    (ArcValuationRing K m n hm hn)
    (criticalNormalClosureArcRawTail K hm hn)
    (criticalNormalClosureArcReciprocalTail K hm hn)
    (criticalGeometricSheetToArcFieldFibre K hm hn σ)
    (criticalNormalClosureArcFieldFibre_coefficients_mem K hm hn
      (criticalGeometricSheetToArcFieldFibre K hm hn σ))

theorem criticalGeometricSheetToArcFibre_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalGeometricSheetToArcFibre K hm hn) := by
  intro σ τ hστ
  apply criticalGeometricSheetToArcFieldFibre_injective K hm hn
  have hmap := congrArg
    (criticalFibreMap (ArcValuationRing K m n hm hn).subtype m n
      (criticalNormalClosureArcRawTail K hm hn)
      (criticalNormalClosureArcReciprocalTail K hm hn)) hστ
  simpa only [criticalFibreMap_criticalGeometricSheetToArcFibre K hm hn] using hmap

end


end GaloisForLFunctions.HTGeometry
