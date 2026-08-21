import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces

/-!
# Diagonal Hasse identifications

The diagonal maps into all completed local fields are injective.  This file upgrades that
local-global separation to ring equivalences onto their diagonal images, for number fields and
rational function fields over finite fields.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- The number-field diagonal as a ring homomorphism into all local completions. -/
noncomputable def numberFieldPlaceDiagonalRingHom
    (K : Type u) [Field K] [NumberField K] :
    K →+* ((v : NumberFieldPlace K) → completion K v) where
  toFun := placeDiagonal K
  map_one' := by
    funext v
    exact map_one (placeEmbedding K v)
  map_mul' x y := by
    funext v
    exact map_mul (placeEmbedding K v) x y
  map_zero' := by
    funext v
    exact map_zero (placeEmbedding K v)
  map_add' x y := by
    funext v
    exact map_add (placeEmbedding K v) x y

/-- The number-field diagonal ring homomorphism is injective. -/
theorem numberFieldPlaceDiagonalRingHom_injective
    (K : Type u) [Field K] [NumberField K] :
    Function.Injective (numberFieldPlaceDiagonalRingHom K) :=
  placeDiagonal_injective K

/-- The number-field diagonal with codomain restricted to its compatible image. -/
noncomputable def numberFieldPlaceDiagonalRingHomToRange
    (K : Type u) [Field K] [NumberField K] :
    K →+* (numberFieldPlaceDiagonalRingHom K).range where
  toFun x := ⟨numberFieldPlaceDiagonalRingHom K x, ⟨x, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact (numberFieldPlaceDiagonalRingHom K).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (numberFieldPlaceDiagonalRingHom K).map_mul x y
  map_zero' := by
    apply Subtype.ext
    exact (numberFieldPlaceDiagonalRingHom K).map_zero
  map_add' x y := by
    apply Subtype.ext
    exact (numberFieldPlaceDiagonalRingHom K).map_add x y

/-- A number field is canonically its compatible diagonal image in all completions. -/
noncomputable def numberFieldPlaceDiagonalRingEquivRange
    (K : Type u) [Field K] [NumberField K] :
    K ≃+* (numberFieldPlaceDiagonalRingHom K).range :=
  RingEquiv.ofBijective (numberFieldPlaceDiagonalRingHomToRange K) ⟨
    fun _ _ h ↦ numberFieldPlaceDiagonalRingHom_injective K (congrArg Subtype.val h),
    fun y ↦ ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩

/-- The number-field diagonal equivalence has the original diagonal family as its underlying map. -/
theorem numberFieldPlaceDiagonalRingEquivRange_apply
    (K : Type u) [Field K] [NumberField K] (x : K) :
    (numberFieldPlaceDiagonalRingEquivRange K x :
      (v : NumberFieldPlace K) → completion K v) = placeDiagonal K x := rfl

/-- The rational-function-field diagonal as a ring homomorphism into all local completions. -/
noncomputable def rationalFunctionPlaceDiagonalRingHom
    (F : Type u) [Field F] [Finite F] :
    RatFunc F →+* ((v : RationalFunctionPlace F) → rationalFunctionCompletion F v) where
  toFun := rationalFunctionPlaceDiagonal F
  map_one' := by
    funext v
    exact map_one (rationalFunctionPlaceEmbedding F v)
  map_mul' x y := by
    funext v
    exact map_mul (rationalFunctionPlaceEmbedding F v) x y
  map_zero' := by
    funext v
    exact map_zero (rationalFunctionPlaceEmbedding F v)
  map_add' x y := by
    funext v
    exact map_add (rationalFunctionPlaceEmbedding F v) x y

/-- The rational-function-field diagonal ring homomorphism is injective. -/
theorem rationalFunctionPlaceDiagonalRingHom_injective
    (F : Type u) [Field F] [Finite F] :
    Function.Injective (rationalFunctionPlaceDiagonalRingHom F) :=
  rationalFunctionPlaceDiagonal_injective F

/-- The rational-function-field diagonal with codomain restricted to its compatible image. -/
noncomputable def rationalFunctionPlaceDiagonalRingHomToRange
    (F : Type u) [Field F] [Finite F] :
    RatFunc F →+* (rationalFunctionPlaceDiagonalRingHom F).range where
  toFun x := ⟨rationalFunctionPlaceDiagonalRingHom F x, ⟨x, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact (rationalFunctionPlaceDiagonalRingHom F).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (rationalFunctionPlaceDiagonalRingHom F).map_mul x y
  map_zero' := by
    apply Subtype.ext
    exact (rationalFunctionPlaceDiagonalRingHom F).map_zero
  map_add' x y := by
    apply Subtype.ext
    exact (rationalFunctionPlaceDiagonalRingHom F).map_add x y

/-- A rational function field is canonically its compatible diagonal image in all completions. -/
noncomputable def rationalFunctionPlaceDiagonalRingEquivRange
    (F : Type u) [Field F] [Finite F] :
    RatFunc F ≃+* (rationalFunctionPlaceDiagonalRingHom F).range :=
  RingEquiv.ofBijective (rationalFunctionPlaceDiagonalRingHomToRange F) ⟨
    fun _ _ h ↦ rationalFunctionPlaceDiagonalRingHom_injective F (congrArg Subtype.val h),
    fun y ↦ ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩

/-- The rational-function-field diagonal equivalence has the original diagonal family as its
underlying map. -/
theorem rationalFunctionPlaceDiagonalRingEquivRange_apply
    (F : Type u) [Field F] [Finite F] (x : RatFunc F) :
    (rationalFunctionPlaceDiagonalRingEquivRange F x :
      (v : RationalFunctionPlace F) → rationalFunctionCompletion F v) =
      rationalFunctionPlaceDiagonal F x := rfl

end GaloisForLFunctions.HTGeometry.ABHN
