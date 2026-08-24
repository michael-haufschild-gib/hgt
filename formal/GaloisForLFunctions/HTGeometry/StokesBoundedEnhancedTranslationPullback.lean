import GaloisForLFunctions.HTGeometry.StokesEnhancedTranslationPullback
import GaloisForLFunctions.HTGeometry.StokesBoundedGeneratedEnhancedVerdier

/-!
# Bounded enhanced translation pullback

Exact enhanced translation pullback preserves canonical cohomological bounds, hence restricts to
bounded derived ind-sheaves. It preserves the bounded projection-generated negligible subcategory
and descends to the bounded generated enhanced Verdier quotient.
-/

open CategoryTheory CategoryTheory.Limits

namespace GaloisForLFunctions.IrregularStokes.EnhancedTranslation

open CompactIndSheaf EnhancedIndPullback

/-- Enhanced translation pullback restricted to bounded derived ind-sheaves. -/
noncomputable abbrev boundedDerivedTranslationPullback (X : TopCat.{0}) (c : ℝ) :
    BoundedDerivedIndSheaf (EnhancedCompactification X) ⥤
      BoundedDerivedIndSheaf (EnhancedCompactification X) :=
  (indTranslationPullback X c).mapBoundedDerivedCategory

/-- Bounded translation agrees with unbounded translation after full inclusion. -/
noncomputable abbrev boundedDerivedTranslationPullbackCompInclusionIso
    (X : TopCat.{0}) (c : ℝ) :
    boundedDerivedTranslationPullback X c ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ derivedTranslationPullback X c :=
  (indTranslationPullback X c).mapBoundedDerivedCategoryCompInclusionIso

noncomputable instance boundedDerivedTranslationPullback_commShift
    (X : TopCat.{0}) (c : ℝ) :
    (boundedDerivedTranslationPullback X c).CommShift ℤ := by
  dsimp [boundedDerivedTranslationPullback]
  infer_instance

noncomputable instance boundedDerivedTranslationPullback_isTriangulated
    (X : TopCat.{0}) (c : ℝ) :
    (boundedDerivedTranslationPullback X c).IsTriangulated := by
  dsimp [boundedDerivedTranslationPullback, Functor.mapBoundedDerivedCategory]
  exact ObjectProperty.isTriangulated_lift
    DerivedCategory.TStructure.t.bounded
    (DerivedCategory.Bounded.ι ⋙ (indTranslationPullback X c).mapDerivedCategory)
    (fun K => (indTranslationPullback X c).mapDerivedCategory_bounded K.obj K.property)

/-- Projection pullback followed by translation pullback is projection pullback in the bounded
derived category. -/
noncomputable def boundedDerivedProjectionCompTranslationIso
    (X : TopCat.{0}) (c : ℝ) :
    boundedDerivedEnhancedIndProjectionPullback X ⋙
        boundedDerivedTranslationPullback X c ≅
      boundedDerivedEnhancedIndProjectionPullback X :=
  Functor.fullyFaithfulCancelRight
    (DerivedCategory.Bounded.ι (C := IndSheaf (EnhancedCompactification X)))
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedDerivedTranslationPullbackCompInclusionIso X c) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedDerivedEnhancedIndProjectionPullbackCompInclusionIso X)
        (derivedTranslationPullback X c) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedProjectionCompTranslationIso X c) ≪≫
      (boundedDerivedEnhancedIndProjectionPullbackCompInclusionIso X).symm)

/-- Bounded derived enhanced translation preserves the bounded generated-negligible envelope. -/
theorem boundedDerivedTranslation_preservesGeneratedNegligible
    (X : TopCat.{0}) (c : ℝ) :
    BoundedGeneratedNegligible X ≤
      (BoundedGeneratedNegligible X).inverseImage
        (boundedDerivedTranslationPullback X c) := by
  letI : ((BoundedGeneratedNegligible X).inverseImage
      (boundedDerivedTranslationPullback X c)).IsStableUnderRetracts :=
    { of_retract := fun r h => (BoundedGeneratedNegligible X).prop_of_retract
        (r.map (boundedDerivedTranslationPullback X c)) h }
  rw [ObjectProperty.triangEnvelope_le_iff]
  rintro K ⟨L, ⟨e⟩⟩
  exact (BoundedGeneratedNegligible X).prop_of_iso
    ((boundedDerivedProjectionCompTranslationIso X c).symm.app L ≪≫
      (boundedDerivedTranslationPullback X c).mapIso e)
    ((BoundedDerivedProjectionImage X).le_triangEnvelope _ ⟨L, ⟨Iso.refl _⟩⟩)

/-- Finite enhanced translation descended to the bounded generated enhanced quotient. -/
noncomputable abbrev boundedQuotientTranslation (X : TopCat.{0}) (c : ℝ) :
    BoundedGeneratedEnhancedQuotient X ⥤ BoundedGeneratedEnhancedQuotient X :=
  VerdierFunctor.mapVerdierQuotient
    (BoundedGeneratedNegligible X) (BoundedGeneratedNegligible X)
    (boundedDerivedTranslationPullback X c)
    (boundedDerivedTranslation_preservesGeneratedNegligible X c)

/-- Canonical square comparing bounded-derived and quotient-level translation. -/
noncomputable abbrev boundedQuotientTranslationSquare (X : TopCat.{0}) (c : ℝ) :
    boundedDerivedTranslationPullback X c ⋙ boundedGeneratedQuotientFunctor X ≅
      boundedGeneratedQuotientFunctor X ⋙ boundedQuotientTranslation X c :=
  VerdierFunctor.mapVerdierQuotientSquare
    (BoundedGeneratedNegligible X) (BoundedGeneratedNegligible X)
    (boundedDerivedTranslationPullback X c)
    (boundedDerivedTranslation_preservesGeneratedNegligible X c)

end GaloisForLFunctions.IrregularStokes.EnhancedTranslation
