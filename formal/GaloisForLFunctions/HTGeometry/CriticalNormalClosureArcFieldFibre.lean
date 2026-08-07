import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcReduction

/-! # Geometric sheets in the normal-closure fibre at the common-scale place -/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

/-- An actual geometric sheet, expressed against the integral tails at the chosen arc place. -/
noncomputable def criticalGeometricSheetToArcFieldFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n →
      criticalFibre (criticalNormalClosure K m n) m n
        ((criticalNormalClosureArcRawTail K hm hn).map
          (ArcValuationRing K m n hm hn).subtype)
        ((criticalNormalClosureArcReciprocalTail K hm hn).map
          (ArcValuationRing K m n hm hn).subtype) := by
  intro σ
  change criticalFibre (criticalNormalClosure K m n) m n
    ((criticalNormalClosureArcRawTail K hm hn).map
      (criticalNormalClosureArcSubtype K hm hn))
    ((criticalNormalClosureArcReciprocalTail K hm hn).map
      (criticalNormalClosureArcSubtype K hm hn))
  rw [criticalNormalClosureArcRawTail_map_subtype K hm hn,
    criticalNormalClosureArcReciprocalTail_map_subtype K hm hn]
  exact criticalGeometricSheetToNormalFibre K m n σ

end


end GaloisForLFunctions.HTGeometry
