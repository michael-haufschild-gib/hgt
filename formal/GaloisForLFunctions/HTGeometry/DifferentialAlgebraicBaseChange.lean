import GaloisForLFunctions.HTGeometry.WickContractedMatroidPersistence

/-!
# Differential-algebraic coefficient-field base change

Differential independence is insensitive to adjoining a differentially algebraic coefficient.
The set-valued persistence theorem already proves the matroid statement.  This module closes the
family/set interface and exposes the coefficient-field law directly for arbitrary indexed
families.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Differential-algebraic base-change law.**  Adjoining one differentially algebraic element
to the coefficient field preserves differential independence of an arbitrary indexed family. -/
theorem DifferentialIndependent.extendScalarsDifferentialAdjoinSingleton
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} {g : E} (hx : DifferentialIndependent F x)
    (hg : DifferentialAlgebraicOver F g) :
    DifferentialIndependent (differentialAdjoin F ({g} : Set E)) x := by
  classical
  let e : ι ≃ Set.range x := Equiv.ofInjective x hx.injective
  have hRange : DiffIndepOn F (Set.range x) := by
    change DifferentialIndependent F
      (Subtype.val : Set.range x → E)
    have h := hx.comp e.symm e.symm.injective
    simpa [e] using h
  have hRangeBase :
      DiffIndepOn (differentialAdjoin F ({g} : Set E)) (Set.range x) :=
    diffIndepOn_differentialAdjoin_singleton_of_differentialAlgebraicOver hg hRange
  have h := hRangeBase.comp e e.injective
  simpa [e] using h

end

end GaloisForLFunctions.HTGeometry
