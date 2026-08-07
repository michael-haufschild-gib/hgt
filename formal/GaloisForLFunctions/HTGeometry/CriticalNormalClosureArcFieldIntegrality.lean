import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcFieldFibre

/-! # Valuative integrality of the normal-closure arc fibre -/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

/-- Projective-boundary exclusion makes every low coefficient of every point in the actual
normal-closure critical fibre integral at the chosen common-scale place. -/
theorem criticalNormalClosureArcFieldFibre_coefficients_mem
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : CriticalNormalClosureArcFieldFibre K hm hn) :
    (∀ i : Fin m, p.1.1.coeff i ∈ ArcValuationRing K m n hm hn) ∧
    ∀ j : Fin n, p.1.2.coeff j ∈ ArcValuationRing K m n hm hn := by
  exact valuationSubring_criticalFibre_coefficients_mem
    (ArcValuationRing K m n hm hn) hm hn
    (criticalNormalClosureArcRawTail K hm hn)
    (criticalNormalClosureArcReciprocalTail K hm hn)
    (criticalNormalClosureArcRawTail_map_residue K hm hn)
    (criticalNormalClosureArcReciprocalTail_map_residue K hm hn)
    p

end


end GaloisForLFunctions.HTGeometry
