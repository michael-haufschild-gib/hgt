import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Abstract enhanced Verdier quotient

The essential image of a full triangulated functor is a triangulated negligible subcategory.
Localizing at morphisms whose cones lie in that image gives a triangulated Verdier quotient,
kills every negligible object, and has the localization descent property.

This isolates the categorical kernel of the enhanced ind-sheaf quotient. It does not construct
ind-sheaves, projection inverse image, quotient adjoints, constructibility, or six operations.
-/

open CategoryTheory Limits Pretriangulated ZeroObject

namespace GaloisForLFunctions.IrregularStokes.AbstractEnhancedVerdier

variable {C D : Type*} [Category* C] [Category* D]
variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
variable [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable [IsTriangulated D]

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full]

/-- Negligible objects: the essential image of the triangulated functor being quotiented out. -/
abbrev Negligible : ObjectProperty D := F.essImage

instance negligibleIsTriangulated : (Negligible F).IsTriangulated := by
  infer_instance

/-- Constructed Verdier quotient by the essential image of `F`. -/
abbrev EnhancedQuotient := (Negligible F).trW.Localization

/-- Canonical functor to the abstract enhanced quotient. -/
abbrev quotientFunctor : D ⥤ EnhancedQuotient F := (Negligible F).trW.Q

/-- The abstract enhanced quotient inherits a triangulated structure. -/
theorem enhancedQuotient_isTriangulated : IsTriangulated (EnhancedQuotient F) := by
  infer_instance

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated D] [F.CommShift ℤ]
  [F.IsTriangulated] [F.Full] in
/-- The quotient functor inverts morphisms whose cones are negligible. -/
theorem quotientFunctor_inverts :
    ((Negligible F).trW).IsInvertedBy (quotientFunctor F) :=
  Localization.inverts (quotientFunctor F) (Negligible F).trW

/-- Every negligible object becomes zero in the quotient. -/
theorem quotient_obj_isZero_of_negligible (X : D) (hX : Negligible F X) :
    IsZero ((quotientFunctor F).obj X) := by
  have hW : (Negligible F).trW (0 : X ⟶ 0) :=
    ObjectProperty.trW.mk' (Negligible F)
      (contractible_distinguished X) hX
  letI : IsIso ((quotientFunctor F).map (0 : X ⟶ 0)) :=
    quotientFunctor_inverts F _ hW
  rw [IsZero.iff_id_eq_zero, ← cancel_mono
    ((quotientFunctor F).map (0 : X ⟶ 0))]
  simp

/-- Every object in the source of `F` maps to zero after quotienting its essential image. -/
theorem quotient_obj_isZero (X : C) :
    IsZero ((quotientFunctor F).obj (F.obj X)) :=
  quotient_obj_isZero_of_negligible F (F.obj X) ⟨X, ⟨Iso.refl _⟩⟩

/-- Any functor inverting the Verdier class descends through the abstract enhanced quotient. -/
noncomputable def descend {E : Type*} [Category* E]
    (G : D ⥤ E) (hG : ((Negligible F).trW).IsInvertedBy G) :
    EnhancedQuotient F ⥤ E :=
  Localization.lift G hG (quotientFunctor F)

/-- Canonical factorization of a functor through the abstract enhanced quotient. -/
noncomputable def descendFactors {E : Type*} [Category* E]
    (G : D ⥤ E) (hG : ((Negligible F).trW).IsInvertedBy G) :
    quotientFunctor F ⋙ descend F G hG ≅ G :=
  Localization.fac G hG (quotientFunctor F)

end GaloisForLFunctions.IrregularStokes.AbstractEnhancedVerdier
