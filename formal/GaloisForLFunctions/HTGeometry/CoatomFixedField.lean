import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# No field lies strictly inside the fixed field of a maximal subgroup

Under the Galois correspondence the intermediate fields below a given one correspond to the
subgroups above its fixing subgroup.  So when that fixing subgroup is maximal, the only fields below
are the base and the field itself.

This is what makes a critical extension field-primitive: its Galois group is the symmetric group and
the extension is the fixed field of a point stabilizer, which is maximal.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **The fixed field of a maximal subgroup has no proper intermediate field below it.** -/
theorem eq_bot_or_eq_of_isCoatom_fixingSubgroup {K M : IntermediateField F E}
    (hK : IsCoatom K.fixingSubgroup) (hMK : M ≤ K) :
    M = ⊥ ∨ M = K := by
  have hle : K.fixingSubgroup ≤ M.fixingSubgroup := IntermediateField.fixingSubgroup_le hMK
  rcases eq_or_lt_of_le hle with heq | hlt
  · refine Or.inr ?_
    have h := congrArg IntermediateField.fixedField heq
    rw [IsGalois.fixedField_fixingSubgroup, IsGalois.fixedField_fixingSubgroup] at h
    exact h.symm
  · refine Or.inl ?_
    have htop : M.fixingSubgroup = ⊤ := hK.2 _ hlt
    have h := congrArg IntermediateField.fixedField htop
    rw [IsGalois.fixedField_fixingSubgroup] at h
    rw [h]
    refine le_antisymm (fun x hx => ?_) bot_le
    have hfix : x ∈ IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) := hx
    exact (IsGalois.fixedField_top (F := F) (E := E)) ▸ hfix

/-- **A point stabilizer in a symmetric group is maximal.**  The natural action is primitive, and a
primitive action has maximal point stabilizers. -/
theorem isCoatom_stabilizer_perm {α : Type*} [Finite α] [Nontrivial α] (a : α) :
    IsCoatom (MulAction.stabilizer (Equiv.Perm α) a) :=
  (MulAction.isCoatom_stabilizer_iff_preprimitive (G := Equiv.Perm α) (X := α) a).2
    inferInstance

end GaloisForLFunctions.HTGeometry
