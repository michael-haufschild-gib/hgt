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
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    refine Subgroup.iSup_induction (fun i => Γ i) (motive := fun g _ => g x = x) hg
      (fun i g hgi => ?_) ?_ (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_)
    · have := (IntermediateField.mem_iInf ..).mp hx i
      rw [IntermediateField.mem_fixedField_iff] at this
      exact this g hgi
    · rfl
    · show (a * b) x = x
      change a (b x) = x
      rw [hb, ha]
    · show a⁻¹ x = x
      have : a (a⁻¹ x) = a x := by rw [ha]
      have h2 : a (a⁻¹ x) = x := by
        change (a * a⁻¹) x = x
        rw [mul_inv_cancel]
        rfl
      have h3 := a.injective (h2.trans ha.symm)
      exact h3
  · intro x hx
    refine (IntermediateField.mem_iInf ..).mpr fun i => ?_
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro g hg
    exact hx g (le_iSup (fun i => Γ i) i hg)

/-- **The deck-closure step.**  If each member of a family of intermediate fields is the fixed field
of the corresponding group, their infimum is the fixed field of the group the family generates. -/
theorem iInf_eq_fixedField_iSup_of_eq {ι : Type*} (Γ : ι → Subgroup (K ≃ₐ[C] K))
    (E : ι → IntermediateField C K) (h : ∀ i, E i = IntermediateField.fixedField (Γ i)) :
    ⨅ i, E i = IntermediateField.fixedField (⨆ i, Γ i) := by
  rw [show (fun i => E i) = fun i => IntermediateField.fixedField (Γ i) from funext h]
  exact iInf_fixedField Γ

end GaloisForLFunctions.HTGeometry
