import GaloisForLFunctions.HTGeometry.Critical.Normal.ClosureArcReduction
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower

/-! # Geometric sheets in the normal-closure fibre at the common-scale place -/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

/-- Critical fibre in the actual normal closure, written using the integral common-scale tails. -/
abbrev CriticalNormalClosureArcFieldFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :=
  criticalFibre (criticalNormalClosure K m n) m n
    ((criticalNormalClosureArcRawTail K hm hn).map
      (ArcValuationRing K m n hm hn).subtype)
    ((criticalNormalClosureArcReciprocalTail K hm hn).map
      (ArcValuationRing K m n hm hn).subtype)

/-- An actual geometric sheet, expressed against the integral tails at the chosen arc place. -/
noncomputable def criticalGeometricSheetToArcFieldFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n →
      CriticalNormalClosureArcFieldFibre K hm hn := by
  intro σ
  let p := criticalGeometricSheetToNormalFibre K m n σ
  refine ⟨p.1, p.2.1, p.2.2.1, ?_⟩
  change (X : (criticalNormalClosure K m n)[X]) ^ (m + n) ∣
    criticalLowProduct
      ((criticalNormalClosureArcRawTail K hm hn).map
        (criticalNormalClosureArcSubtype K hm hn))
      ((criticalNormalClosureArcReciprocalTail K hm hn).map
        (criticalNormalClosureArcSubtype K hm hn)) p.1.1 p.1.2 - 1
  rw [criticalNormalClosureArcRawTail_map_subtype K hm hn,
    criticalNormalClosureArcReciprocalTail_map_subtype K hm hn]
  exact p.2.2.2

end


end GaloisForLFunctions.HTGeometry
