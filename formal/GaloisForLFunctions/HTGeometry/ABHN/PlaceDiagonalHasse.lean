import GaloisForLFunctions.HTGeometry.ABHN.Places

/-!
# Hasse separation by all number-field places

The canonical embeddings into finite and infinite completions assemble into a ring homomorphism.
It identifies the global number field with the subring of all-place profiles that are globally
realized.  In particular, equality at every place is equivalent to global equality.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open NumberField

universe u

/-- The all-place diagonal embedding as a ring homomorphism. -/
noncomputable def placeDiagonalRingHom
    (K : Type u) [Field K] [NumberField K] :
    K →+* ((v : NumberFieldPlace K) → completion K v) where
  toFun := placeDiagonal K
  map_one' := by funext v; exact map_one (placeEmbedding K v)
  map_mul' x y := by funext v; exact map_mul (placeEmbedding K v) x y
  map_zero' := by funext v; exact map_zero (placeEmbedding K v)
  map_add' x y := by funext v; exact map_add (placeEmbedding K v) x y

@[simp] theorem placeDiagonalRingHom_apply
    (K : Type u) [Field K] [NumberField K] (x : K) (v : NumberFieldPlace K) :
    placeDiagonalRingHom K x v = placeEmbedding K v x :=
  rfl

/-- The all-place diagonal ring homomorphism is injective. -/
theorem placeDiagonalRingHom_injective
    (K : Type u) [Field K] [NumberField K] :
    Function.Injective (placeDiagonalRingHom K) :=
  placeDiagonal_injective K

/-- A number field is ring-equivalent to the all-place profiles that it actually realizes. -/
noncomputable def placeDiagonalHasseEquivRealizedProfiles
    (K : Type u) [Field K] [NumberField K] :
    K ≃+* RingHom.range (placeDiagonalRingHom K) :=
  RingEquiv.ofBijective (RingHom.rangeRestrict (placeDiagonalRingHom K))
    ⟨fun _ _ h => placeDiagonal_injective K (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- Two global elements are equal exactly when their images agree at every finite and infinite
place. -/
theorem placeDiagonal_congr_hasse_iff
    (K : Type u) [Field K] [NumberField K] (x y : K) :
    (∀ v : NumberFieldPlace K, placeEmbedding K v x = placeEmbedding K v y) ↔ x = y := by
  constructor
  · intro h
    apply placeDiagonal_injective K
    funext v
    exact h v
  · rintro rfl v
    rfl

end GaloisForLFunctions.HTGeometry.ABHN
