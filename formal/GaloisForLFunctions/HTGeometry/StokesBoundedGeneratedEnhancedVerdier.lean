import GaloisForLFunctions.HTGeometry.StokesDerivedEnhancedIndPullback
import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Bounded generated enhanced Verdier quotient

The thick triangulated envelope of bounded derived projection pullbacks gives an unconditional
bounded negligible subcategory. Its Verdier quotient kills all bounded base-pulled objects and
has the localization descent property.
-/

open CategoryTheory Limits Pretriangulated ZeroObject

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CompactIndSheaf

/-- Essential image of bounded derived pullback from the base. -/
abbrev BoundedDerivedProjectionImage (X : TopCat.{0}) : ObjectProperty
    (BoundedDerivedIndSheaf (EnhancedCompactification X)) :=
  (boundedDerivedEnhancedIndProjectionPullback X).essImage

noncomputable instance boundedDerivedProjectionImage_nonempty (X : TopCat.{0}) :
    (BoundedDerivedProjectionImage X).Nonempty :=
  ⟨(boundedDerivedEnhancedIndProjectionPullback X).obj 0,
    ⟨0, ⟨Iso.refl _⟩⟩⟩

/-- Bounded negligible subcategory generated thickly by base-pulled objects. -/
abbrev BoundedGeneratedNegligible (X : TopCat.{0}) : ObjectProperty
    (BoundedDerivedIndSheaf (EnhancedCompactification X)) :=
  (BoundedDerivedProjectionImage X).triangEnvelope

instance boundedGeneratedNegligible_isTriangulated (X : TopCat.{0}) :
    (BoundedGeneratedNegligible X).IsTriangulated := by
  infer_instance

/-- Bounded enhanced quotient by the generated negligible subcategory. -/
abbrev BoundedGeneratedEnhancedQuotient (X : TopCat.{0}) :=
  (BoundedGeneratedNegligible X).trW.Localization

/-- Canonical functor to the bounded generated enhanced quotient. -/
noncomputable abbrev boundedGeneratedQuotientFunctor (X : TopCat.{0}) :
    BoundedDerivedIndSheaf (EnhancedCompactification X) ⥤
      BoundedGeneratedEnhancedQuotient X :=
  (BoundedGeneratedNegligible X).trW.Q

/-- Bounded generated enhanced quotient inherits a triangulated structure. -/
theorem boundedGeneratedEnhancedQuotient_isTriangulated (X : TopCat.{0}) :
    IsTriangulated (BoundedGeneratedEnhancedQuotient X) := by
  infer_instance

/-- Bounded quotient functor inverts morphisms whose cones are generated-negligible. -/
theorem boundedGeneratedQuotientFunctor_inverts (X : TopCat.{0}) :
    ((BoundedGeneratedNegligible X).trW).IsInvertedBy
      (boundedGeneratedQuotientFunctor X) :=
  Localization.inverts (boundedGeneratedQuotientFunctor X) (BoundedGeneratedNegligible X).trW

/-- Every bounded generated-negligible object becomes zero in the quotient. -/
theorem boundedGeneratedQuotient_obj_isZero_of_negligible (X : TopCat.{0})
    (K : BoundedDerivedIndSheaf (EnhancedCompactification X))
    (hK : BoundedGeneratedNegligible X K) :
    IsZero ((boundedGeneratedQuotientFunctor X).obj K) := by
  have hW : (BoundedGeneratedNegligible X).trW (0 : K ⟶ 0) :=
    ObjectProperty.trW.mk' (BoundedGeneratedNegligible X)
      (contractible_distinguished K) hK
  letI : IsIso ((boundedGeneratedQuotientFunctor X).map (0 : K ⟶ 0)) :=
    boundedGeneratedQuotientFunctor_inverts X _ hW
  rw [IsZero.iff_id_eq_zero, ← cancel_mono
    ((boundedGeneratedQuotientFunctor X).map (0 : K ⟶ 0))]
  simp

/-- Every bounded derived object pulled back from the base becomes zero in the quotient. -/
theorem boundedGeneratedQuotient_obj_isZero (X : TopCat.{0})
    (K : BoundedDerivedIndSheaf X) :
    IsZero ((boundedGeneratedQuotientFunctor X).obj
      ((boundedDerivedEnhancedIndProjectionPullback X).obj K)) :=
  boundedGeneratedQuotient_obj_isZero_of_negligible X _
    ((BoundedDerivedProjectionImage X).le_triangEnvelope _ ⟨K, ⟨Iso.refl _⟩⟩)

/-- Any functor inverting the bounded generated Verdier class descends through the quotient. -/
noncomputable def boundedGeneratedDescend {E : Type*} [Category* E] (X : TopCat.{0})
    (G : BoundedDerivedIndSheaf (EnhancedCompactification X) ⥤ E)
    (hG : ((BoundedGeneratedNegligible X).trW).IsInvertedBy G) :
    BoundedGeneratedEnhancedQuotient X ⥤ E :=
  Localization.lift G hG (boundedGeneratedQuotientFunctor X)

/-- Canonical factorization through the bounded generated enhanced quotient. -/
noncomputable def boundedGeneratedDescendFactors {E : Type*} [Category* E]
    (X : TopCat.{0})
    (G : BoundedDerivedIndSheaf (EnhancedCompactification X) ⥤ E)
    (hG : ((BoundedGeneratedNegligible X).trW).IsInvertedBy G) :
    boundedGeneratedQuotientFunctor X ⋙ boundedGeneratedDescend X G hG ≅ G :=
  Localization.fac G hG (boundedGeneratedQuotientFunctor X)

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
