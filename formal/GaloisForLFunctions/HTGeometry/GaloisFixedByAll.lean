import Mathlib.FieldTheory.Galois.Basic

/-!
# An element fixed by the whole Galois group lies in the base

For a finite Galois extension the fixed field of the whole automorphism group is the base field, so
an element moved by no automorphism is already a scalar.

Applied to a compositum this says that an element of one factor fixed by every automorphism over
the other factor lies in their intersection, which is the step identifying the fixed field of the
restricted Galois group.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An element fixed by every automorphism of a finite Galois extension lies in the base.** -/
theorem mem_bot_of_forall_fixed {M L : Type*} [Field M] [Field L] [Algebra M L]
    [FiniteDimensional M L] [IsGalois M L] {x : L} (h : ∀ σ : L ≃ₐ[M] L, σ x = x) :
    x ∈ (⊥ : IntermediateField M L) := by
  rw [← IsGalois.fixedField_top (F := M) (E := L), IntermediateField.mem_fixedField_iff]
  intro σ _
  exact h σ

theorem exists_algebraMap_of_forall_fixed {M L : Type*} [Field M] [Field L] [Algebra M L]
    [FiniteDimensional M L] [IsGalois M L] {x : L} (h : ∀ σ : L ≃ₐ[M] L, σ x = x) :
    ∃ y : M, algebraMap M L y = x :=
  IntermediateField.mem_bot.1 (mem_bot_of_forall_fixed h)

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **An element of one factor of a compositum fixed by every automorphism over the other factor
lies in the intersection.** -/
theorem mem_inf_of_forall_fixed {E M : IntermediateField F L}
    [FiniteDimensional M L] [IsGalois M L] {x : L} (hxE : x ∈ E)
    (h : ∀ σ : L ≃ₐ[M] L, σ x = x) : x ∈ E ⊓ M := by
  refine ⟨hxE, ?_⟩
  obtain ⟨y, hy⟩ := exists_algebraMap_of_forall_fixed h
  rw [← hy]
  exact y.2

end GaloisForLFunctions.HTGeometry
