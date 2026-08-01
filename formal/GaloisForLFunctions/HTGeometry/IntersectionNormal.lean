import Mathlib.FieldTheory.Galois.Basic

/-!
# The intersection of two normal subextensions

An automorphism of the ambient field carries each of two normal subextensions to itself, hence
carries their intersection to itself, so the intersection is normal.

Reading the intersection inside the first of the two factors keeps it normal, and in characteristic
zero normal means Galois, so the subgroup fixing it is a normal subgroup.  That is the group-side
hypothesis of the base change step.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem map_inf_of_algEquiv (E M : IntermediateField F L) (σ : L ≃ₐ[F] L) :
    (E ⊓ M).map (σ : L →ₐ[F] L) = E.map (σ : L →ₐ[F] L) ⊓ M.map (σ : L →ₐ[F] L) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyE, hyM⟩, rfl⟩
    exact ⟨⟨y, hyE, rfl⟩, ⟨y, hyM, rfl⟩⟩
  · rintro ⟨⟨y, hyE, hy⟩, ⟨z, hzM, hz⟩⟩
    have hyz : y = z := σ.injective (hy.trans hz.symm)
    exact ⟨y, ⟨hyE, hyz ▸ hzM⟩, hy⟩

/-- **The intersection of two normal subextensions is normal.** -/
instance normal_inf (E M : IntermediateField F L) [Normal F L] [Normal F E] [Normal F M] :
    Normal F (E ⊓ M : IntermediateField F L) := by
  rw [IntermediateField.normal_iff_forall_map_eq']
  intro σ
  rw [map_inf_of_algEquiv, IntermediateField.normal_iff_forall_map_eq'.1 (by infer_instance) σ,
    IntermediateField.normal_iff_forall_map_eq'.1 (by infer_instance : Normal F M) σ]

end GaloisForLFunctions.HTGeometry
