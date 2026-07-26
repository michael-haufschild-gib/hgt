import GaloisForLFunctions.HTGeometry.ClockPeriodCommensurabilityBoundary

/-!
# Consistency of the multiple-sine regime interface

The regime interface bundles the two halves of the multiple-sine dichotomy.  With no clock
directions the nonreal-ratio half is vacuous and the commensurable half holds for an embedded
constant, so the interface is consistent.  Its substantive realization is the analytic dichotomy for
the actual multiple sine, which is not available in the corpus.
-/

namespace GaloisForLFunctions.HTGeometry

/-- With no clock directions the regime interface is realized by an embedded constant. -/
theorem multipleSineDifferentialRegimeInput_isEmpty
    (F E ι : Type*) [Field F] [Field E] [Algebra F E] [Differential E] [IsEmpty ι] :
    MultipleSineDifferentialRegimeInput F E ι (fun _ => (0 : E)) := by
  refine ⟨?_, ?_⟩
  · intro ω _
    simpa using differentialAlgebraicOver_algebraMap (F := F) (E := E) 0
  · rintro ω ⟨i, _, _, _⟩
    exact isEmptyElim i

end GaloisForLFunctions.HTGeometry
