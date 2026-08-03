import GaloisForLFunctions.HTGeometry.StableCoreFunctoriality

/-!
# Stable cores restricted to commuting fixed fields

If an algebra endomorphism commutes with a symmetry subgroup, it restricts to that subgroup's
fixed field.  This module proves that the stable core of the restriction, mapped back into the
ambient field, is exactly the intersection of the ambient stable core with the fixed field.  This
is the exact field-theoretic finite-holonomy step in isogeny-tail arguments; finiteness is not
needed for the identity itself.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Restriction of an endomorphism to the fixed field of a commuting symmetry subgroup. -/
def fixedFieldEndomorphism
    (phi : L →ₐ[K] L) (H : Subgroup (L ≃ₐ[K] L))
    (hcomm : ∀ sigma ∈ H, ∀ x, phi (sigma x) = sigma (phi x)) :
    IntermediateField.fixedField H →ₐ[K] IntermediateField.fixedField H :=
  (phi.comp (IntermediateField.fixedField H).val).codRestrict
    (IntermediateField.fixedField H).toSubalgebra (by
      intro x
      change phi x ∈ IntermediateField.fixedField H
      rw [IntermediateField.mem_fixedField_iff]
      intro sigma hsigma
      rw [← hcomm sigma hsigma x]
      congr 1
      exact ((IntermediateField.mem_fixedField_iff (H := H) (x : L)).mp x.2) sigma hsigma)

@[simp]
theorem fixedFieldEndomorphism_apply
    (phi : L →ₐ[K] L) (H : Subgroup (L ≃ₐ[K] L))
    (hcomm : ∀ sigma ∈ H, ∀ x, phi (sigma x) = sigma (phi x))
    (x : IntermediateField.fixedField H) :
    (fixedFieldEndomorphism phi H hcomm x : L) = phi x := rfl

/-- Restricting a commuting endomorphism to a fixed field commutes with all iterates. -/
theorem fixedFieldEndomorphism_pow_apply
    (phi : L →ₐ[K] L) (H : Subgroup (L ≃ₐ[K] L))
    (hcomm : ∀ sigma ∈ H, ∀ x, phi (sigma x) = sigma (phi x))
    (n : ℕ) (x : IntermediateField.fixedField H) :
    ((fixedFieldEndomorphism phi H hcomm ^ n) x : L) = (phi ^ n) x := by
  symm
  exact algHom_pow_intertwine (IntermediateField.fixedField H).val
    (fixedFieldEndomorphism phi H hcomm) phi (fun _ => rfl) n x

/-- Stable core after restriction to a commuting fixed field is exactly the intersection of the
ambient stable core with that fixed field. -/
theorem map_stableRangeCore_fixedFieldEndomorphism
    (phi : L →ₐ[K] L) (H : Subgroup (L ≃ₐ[K] L))
    (hcomm : ∀ sigma ∈ H, ∀ x, phi (sigma x) = sigma (phi x)) :
    IntermediateField.map (IntermediateField.fixedField H).val
        (stableRangeCore (fixedFieldEndomorphism phi H hcomm)) =
      stableRangeCore phi ⊓ IntermediateField.fixedField H := by
  apply le_antisymm
  · apply le_inf
    · exact map_stableRangeCore_le_of_intertwine
        (IntermediateField.fixedField H).val
        (fixedFieldEndomorphism phi H hcomm) phi (fun _ => rfl)
    · intro x hx
      rw [IntermediateField.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
  · intro x hx
    rw [IntermediateField.mem_inf] at hx
    let xH : IntermediateField.fixedField H := ⟨x, hx.2⟩
    rw [IntermediateField.mem_map]
    refine ⟨xH, ?_, rfl⟩
    rw [mem_stableRangeCore_iff] at hx ⊢
    intro n
    obtain ⟨y, hy⟩ := hx.1 n
    have hyH : y ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro sigma hsigma
      apply (phi ^ n).injective
      calc
        (phi ^ n) (sigma y) = sigma ((phi ^ n) y) :=
          algHom_pow_intertwine sigma.toAlgHom phi phi
            (hcomm sigma hsigma) n y
        _ = sigma x := congrArg sigma hy
        _ = x := ((IntermediateField.mem_fixedField_iff (H := H) x).mp hx.2) sigma hsigma
        _ = (phi ^ n) y := hy.symm
    let yH : IntermediateField.fixedField H := ⟨y, hyH⟩
    refine ⟨yH, ?_⟩
    apply Subtype.ext
    change ((fixedFieldEndomorphism phi H hcomm ^ n) yH : L) = x
    rw [fixedFieldEndomorphism_pow_apply]
    exact hy

end

end GaloisForLFunctions.HTGeometry
