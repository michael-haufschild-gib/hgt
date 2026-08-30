import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Adjoining one element to a generated field

Generating with one more element is the same as adjoining that element to the field the rest
generates.  This is the step that turns a jet field into a tower with a single top step.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Adjoining one element to a generated field.** -/
theorem adjoin_insert_eq_restrictScalars {F E : Type*} [Field F] [Field E] [Algebra F E]
    (S : Set E) (x : E) :
    (IntermediateField.adjoin ↥(IntermediateField.adjoin F S) ({x} : Set E)).restrictScalars F
      = IntermediateField.adjoin F (insert x S) := by
  rw [IntermediateField.adjoin_adjoin_left, Set.union_singleton]

end GaloisForLFunctions.HTGeometry
