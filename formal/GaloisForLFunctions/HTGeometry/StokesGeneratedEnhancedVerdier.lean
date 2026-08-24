import GaloisForLFunctions.HTGeometry.StokesDerivedEnhancedIndPullback
import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Generated enhanced Verdier quotient

The thick triangulated envelope of the derived projection-pullback image is an unconditional
negligible subcategory. Its Verdier quotient is triangulated, kills every base-pulled object, and
has the localization descent property. Equality with the bare essential image remains equivalent
to the separate fullness problem for derived projection pullback.
-/

open CategoryTheory Limits Pretriangulated ZeroObject

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CompactIndSheaf

/-- Essential image of derived pullback from the base. -/
abbrev DerivedProjectionImage (X : TopCat.{0}) : ObjectProperty
    (DerivedIndSheaf (EnhancedCompactification X)) :=
  (derivedEnhancedIndProjectionPullback X).essImage

noncomputable instance derivedProjectionImage_nonempty (X : TopCat.{0}) :
    (DerivedProjectionImage X).Nonempty :=
  ⟨(derivedEnhancedIndProjectionPullback X).obj 0,
    ⟨0, ⟨Iso.refl _⟩⟩⟩

/-- Unconditional negligible subcategory: thick triangulated envelope of base-pulled objects. -/
abbrev GeneratedNegligible (X : TopCat.{0}) : ObjectProperty
    (DerivedIndSheaf (EnhancedCompactification X)) :=
  (DerivedProjectionImage X).triangEnvelope

instance generatedNegligible_isTriangulated (X : TopCat.{0}) :
    (GeneratedNegligible X).IsTriangulated := by
  infer_instance

/-- Unbounded enhanced quotient by the generated negligible subcategory. -/
abbrev GeneratedEnhancedQuotient (X : TopCat.{0}) :=
  (GeneratedNegligible X).trW.Localization

/-- Canonical functor to the generated enhanced quotient. -/
noncomputable abbrev generatedQuotientFunctor (X : TopCat.{0}) :
    DerivedIndSheaf (EnhancedCompactification X) ⥤ GeneratedEnhancedQuotient X :=
  (GeneratedNegligible X).trW.Q

/-- Generated enhanced quotient inherits a triangulated structure. -/
theorem generatedEnhancedQuotient_isTriangulated (X : TopCat.{0}) :
    IsTriangulated (GeneratedEnhancedQuotient X) := by
  infer_instance

/-- Quotient functor inverts morphisms whose cones are generated-negligible. -/
theorem generatedQuotientFunctor_inverts (X : TopCat.{0}) :
    ((GeneratedNegligible X).trW).IsInvertedBy (generatedQuotientFunctor X) :=
  Localization.inverts (generatedQuotientFunctor X) (GeneratedNegligible X).trW

/-- Every generated-negligible object becomes zero in the quotient. -/
theorem generatedQuotient_obj_isZero_of_negligible (X : TopCat.{0})
    (K : DerivedIndSheaf (EnhancedCompactification X)) (hK : GeneratedNegligible X K) :
    IsZero ((generatedQuotientFunctor X).obj K) := by
  have hW : (GeneratedNegligible X).trW (0 : K ⟶ 0) :=
    ObjectProperty.trW.mk' (GeneratedNegligible X)
      (contractible_distinguished K) hK
  letI : IsIso ((generatedQuotientFunctor X).map (0 : K ⟶ 0)) :=
    generatedQuotientFunctor_inverts X _ hW
  rw [IsZero.iff_id_eq_zero, ← cancel_mono
    ((generatedQuotientFunctor X).map (0 : K ⟶ 0))]
  simp

/-- Every derived object pulled back from the base becomes zero in the generated quotient. -/
theorem generatedQuotient_obj_isZero (X : TopCat.{0}) (K : DerivedIndSheaf X) :
    IsZero ((generatedQuotientFunctor X).obj
      ((derivedEnhancedIndProjectionPullback X).obj K)) :=
  generatedQuotient_obj_isZero_of_negligible X _
    ((DerivedProjectionImage X).le_triangEnvelope _ ⟨K, ⟨Iso.refl _⟩⟩)

/-- Any functor inverting the generated Verdier class descends through the quotient. -/
noncomputable def generatedDescend {E : Type*} [Category* E] (X : TopCat.{0})
    (G : DerivedIndSheaf (EnhancedCompactification X) ⥤ E)
    (hG : ((GeneratedNegligible X).trW).IsInvertedBy G) :
    GeneratedEnhancedQuotient X ⥤ E :=
  Localization.lift G hG (generatedQuotientFunctor X)

/-- Canonical factorization through the generated enhanced quotient. -/
noncomputable def generatedDescendFactors {E : Type*} [Category* E] (X : TopCat.{0})
    (G : DerivedIndSheaf (EnhancedCompactification X) ⥤ E)
    (hG : ((GeneratedNegligible X).trW).IsInvertedBy G) :
    generatedQuotientFunctor X ⋙ generatedDescend X G hG ≅ G :=
  Localization.fac G hG (generatedQuotientFunctor X)

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
