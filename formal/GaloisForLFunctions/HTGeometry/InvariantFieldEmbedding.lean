import Mathlib.FieldTheory.IntermediateField.Basic

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {L M : Type*} [Field L] [Field M]
variable (f : L →+* M) (σ : M ≃+* M)
variable (hstable : ∀ x : L, ∃ y : L, f y = σ (f x))

private def invariantEmbeddingHom : L →+* L where
  toFun x := Classical.choose (hstable x)
  map_one' := f.injective (by
    rw [Classical.choose_spec (hstable 1), map_one, map_one])
  map_zero' := f.injective (by
    rw [Classical.choose_spec (hstable 0), map_zero, map_zero])
  map_add' x y := f.injective (by
    rw [Classical.choose_spec (hstable (x + y)), map_add, map_add, map_add,
      Classical.choose_spec (hstable x), Classical.choose_spec (hstable y)])
  map_mul' x y := f.injective (by
    rw [Classical.choose_spec (hstable (x * y)), map_mul, map_mul, map_mul,
      Classical.choose_spec (hstable x), Classical.choose_spec (hstable y)])

private theorem invariantEmbeddingHom_map (x : L) :
    f (invariantEmbeddingHom f σ hstable x) = σ (f x) := Classical.choose_spec (hstable x)

private theorem invariantEmbeddingHom_involutive (hinv : Function.Involutive σ) :
    Function.Involutive (invariantEmbeddingHom f σ hstable) := by
  intro x
  apply f.injective
  rw [invariantEmbeddingHom_map, invariantEmbeddingHom_map, hinv (f x)]

/-- An ambient involution restricts through a field embedding with invariant image. -/
def ringEquivOfInvariantEmbedding (hinv : Function.Involutive σ) : L ≃+* L where
  __ := invariantEmbeddingHom f σ hstable
  invFun := invariantEmbeddingHom f σ hstable
  left_inv := invariantEmbeddingHom_involutive f σ hstable hinv
  right_inv := invariantEmbeddingHom_involutive f σ hstable hinv

theorem ringEquivOfInvariantEmbedding_map (hinv : Function.Involutive σ) (x : L) :
    f (ringEquivOfInvariantEmbedding f σ hstable hinv x) = σ (f x) :=
  invariantEmbeddingHom_map f σ hstable x

theorem ringEquivOfInvariantEmbedding_involutive (hinv : Function.Involutive σ) :
    Function.Involutive (ringEquivOfInvariantEmbedding f σ hstable hinv) :=
  invariantEmbeddingHom_involutive f σ hstable hinv

end GaloisForLFunctions.HTGeometry
