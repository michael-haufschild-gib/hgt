import GaloisForLFunctions.HTGeometry.CoatomFixedField

/-!
# One element outside the base generates a field-primitive extension

If an intermediate field has maximal fixing subgroup, then it has no proper intermediate field
below it, so any of its elements that is not already in the base generates it.

This is the mechanism by which a single postcritical observation resolves a critical extension: the
critical extension is field-primitive, and the postcritical reciprocal coefficient is not in the
critical field, so it generates.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **An element of a field-primitive extension that is not in the base generates it.** -/
theorem adjoin_eq_of_notMem_of_isCoatom {K : IntermediateField F E}
    (hK : IsCoatom K.fixingSubgroup) {v : E} (hv : v ∈ K)
    (hvnot : v ∉ (⊥ : IntermediateField F E)) :
    IntermediateField.adjoin F {v} = K := by
  have hle : IntermediateField.adjoin F {v} ≤ K :=
    IntermediateField.adjoin_le_iff.2 (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hv)
  rcases eq_bot_or_eq_of_isCoatom_fixingSubgroup hK hle with hbot | htop
  · exact absurd (hbot ▸ IntermediateField.mem_adjoin_simple_self F v) hvnot
  · exact htop

/-- **The degree of a field-primitive extension is the degree of the generator.**  Stated as the
equality of the generated field with the extension, in the form a minimal polynomial argument
consumes. -/
theorem adjoin_eq_top_of_notMem_of_isCoatom
    (hK : IsCoatom (⊤ : IntermediateField F E).fixingSubgroup) {v : E}
    (hvnot : v ∉ (⊥ : IntermediateField F E)) :
    IntermediateField.adjoin F {v} = ⊤ :=
  adjoin_eq_of_notMem_of_isCoatom hK (IntermediateField.mem_top) hvnot

end GaloisForLFunctions.HTGeometry
