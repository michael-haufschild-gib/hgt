import GaloisForLFunctions.HTGeometry.IsogenyDegreeFixedField
import Mathlib.FieldTheory.Galois.Basic

/-!
# Fixed fields turn suprema of groups into infima of fields

An element fixed by every member of a family of automorphism groups is fixed by the subgroup they
generate, because the elements they fix form a subgroup.  So the infimum of the fixed fields of a
family is the fixed field of the supremum of the family.

Applied to the deck groups of an isogeny tower, this is the step from
`alpha^{n*} K = K^{Gamma_n}` for each `n` to
`⋂_n alpha^{n*} K = K^{⋃_n Gamma_n}`, which is the deck-closure theorem before the topological
closure is taken.

* `iInf_fixedField`;
* `iInf_eq_fixedField_iSup_of_eq`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- **The infimum of fixed fields is the fixed field of the supremum.** -/
theorem iInf_fixedField {ι : Type*} (Γ : ι → Subgroup (K ≃ₐ[C] K)) :
    ⨅ i, IntermediateField.fixedField (Γ i)
      = IntermediateField.fixedField (⨆ i, Γ i) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hmem : ∀ i, x ∈ IntermediateField.fixedField (Γ i) := by
      intro i
      have hset : x ∈ (↑(⨅ i, IntermediateField.fixedField (Γ i)) : Set K) := hx
      rw [IntermediateField.coe_iInf] at hset
      exact Set.mem_iInter.mp hset i
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    refine Subgroup.iSup_induction (C := fun g : K ≃ₐ[C] K => g x = x) (fun i => Γ i) hg
      (fun i a hai => ?_) rfl (fun a b ha hb => ?_)
    · have h := hmem i
      rw [IntermediateField.mem_fixedField_iff] at h
      exact h a hai
    · show a (b x) = x
      rw [hb, ha]
  · intro x hx
    have hset : x ∈ (↑(⨅ i, IntermediateField.fixedField (Γ i)) : Set K) := by
      rw [IntermediateField.coe_iInf]
      refine Set.mem_iInter.mpr fun i => ?_
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      rw [IntermediateField.mem_fixedField_iff] at hx
      intro g hg
      exact hx g (le_iSup (fun i => Γ i) i hg)
    exact hset

/-- **The deck-closure step.**  If each member of a family of intermediate fields is the fixed field
of the corresponding group, their infimum is the fixed field of the group the family generates. -/
theorem iInf_eq_fixedField_iSup_of_eq {ι : Type*} (Γ : ι → Subgroup (K ≃ₐ[C] K))
    (E : ι → IntermediateField C K) (h : ∀ i, E i = IntermediateField.fixedField (Γ i)) :
    ⨅ i, E i = IntermediateField.fixedField (⨆ i, Γ i) := by
  rw [show (fun i => E i) = fun i => IntermediateField.fixedField (Γ i) from funext h]
  exact iInf_fixedField Γ

end GaloisForLFunctions.HTGeometry
