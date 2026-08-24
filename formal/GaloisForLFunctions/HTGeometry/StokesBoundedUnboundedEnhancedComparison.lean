import GaloisForLFunctions.HTGeometry.StokesEnhancedExponentialObject
import GaloisForLFunctions.HTGeometry.StokesVerdierFunctorDescent

/-!
# Bounded-to-unbounded enhanced comparison

The standard inclusion of bounded into unbounded derived ind-sheaves carries the bounded thick
envelope of projection pullbacks into its unbounded analogue. It therefore descends to a
triangulated functor between the generated enhanced Verdier quotients. The localization square
also identifies bounded compactified exponential objects with their unbounded realizations.
-/

open CategoryTheory Limits Pretriangulated ZeroObject

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CompactIndSheaf EnhancedExponential EnhancedTranslation

/-- Bounded inclusion carries the bounded generated-negligible envelope into the unbounded one. -/
theorem boundedInclusion_preservesGeneratedNegligible (X : TopCat.{0}) :
    BoundedGeneratedNegligible X ≤
      (GeneratedNegligible X).inverseImage DerivedCategory.Bounded.ι := by
  letI : ((GeneratedNegligible X).inverseImage
      DerivedCategory.Bounded.ι).IsStableUnderRetracts :=
    { of_retract := fun r h => (GeneratedNegligible X).prop_of_retract
        (r.map DerivedCategory.Bounded.ι) h }
  rw [ObjectProperty.triangEnvelope_le_iff]
  rintro K ⟨L, ⟨e⟩⟩
  exact (GeneratedNegligible X).prop_of_iso
    ((boundedDerivedEnhancedIndProjectionPullbackCompInclusionIso X).symm.app L ≪≫
      DerivedCategory.Bounded.ι.mapIso e)
    ((DerivedProjectionImage X).le_triangEnvelope _ ⟨_, ⟨Iso.refl _⟩⟩)

/-- Canonical triangulated comparison from bounded to unbounded generated enhanced quotients. -/
noncomputable abbrev boundedToUnboundedEnhanced (X : TopCat.{0}) :
    BoundedGeneratedEnhancedQuotient X ⥤ GeneratedEnhancedQuotient X :=
  VerdierFunctor.mapVerdierQuotient
    (BoundedGeneratedNegligible X) (GeneratedNegligible X)
    DerivedCategory.Bounded.ι (boundedInclusion_preservesGeneratedNegligible X)

/-- The quotient comparison commutes with bounded inclusion up to the localization isomorphism. -/
noncomputable abbrev boundedToUnboundedEnhancedSquare (X : TopCat.{0}) :
    DerivedCategory.Bounded.ι ⋙ generatedQuotientFunctor X ≅
      boundedGeneratedQuotientFunctor X ⋙ boundedToUnboundedEnhanced X :=
  VerdierFunctor.mapVerdierQuotientSquare
    (BoundedGeneratedNegligible X) (GeneratedNegligible X)
    DerivedCategory.Bounded.ι (boundedInclusion_preservesGeneratedNegligible X)

/-- Objectwise form of the bounded-to-unbounded localization square. -/
noncomputable abbrev boundedToUnboundedEnhanced_objIso (X : TopCat.{0})
    (K : BoundedDerivedIndSheaf (EnhancedCompactification X)) :
    (boundedToUnboundedEnhanced X).obj ((boundedGeneratedQuotientFunctor X).obj K) ≅
      (generatedQuotientFunctor X).obj (DerivedCategory.Bounded.ι.obj K) :=
  (boundedToUnboundedEnhancedSquare X).symm.app K

/-- Bounded compactified exponential objects compare canonically with unbounded ones. -/
noncomputable def compactifiedExponential_boundedToUnboundedIso (X : TopCat.{0})
    [CompactSpace X] (φ : X → ℝ) (hφ : Continuous φ) :
    (boundedToUnboundedEnhanced X).obj
        (compactifiedExponentialBoundedEnhancedObject X φ hφ) ≅
      compactifiedExponentialEnhancedObject X φ hφ :=
  boundedToUnboundedEnhanced_objIso X
    (compactifiedExponentialBoundedDerivedObject X φ hφ)

/-- Before bounded localization, derived translation compatibility and both localization squares
identify the two bounded-to-unbounded translation composites. -/
noncomputable def boundedToUnboundedEnhancedTranslationPrequotientIso
    (X : TopCat.{0}) (c : ℝ) :
    boundedGeneratedQuotientFunctor X ⋙
        (boundedQuotientTranslation X c ⋙ boundedToUnboundedEnhanced X) ≅
      boundedGeneratedQuotientFunctor X ⋙
        (boundedToUnboundedEnhanced X ⋙ quotientTranslation X c) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedQuotientTranslationSquare X c).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedToUnboundedEnhancedSquare X).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedDerivedTranslationPullbackCompInclusionIso X c) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (quotientTranslationSquare X c) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedToUnboundedEnhancedSquare X) _ ≪≫
    Functor.associator _ _ _

/-- Bounded-to-unbounded enhanced comparison intertwines finite translation actions. -/
noncomputable def boundedToUnboundedEnhancedTranslationIso (X : TopCat.{0}) (c : ℝ) :
    boundedQuotientTranslation X c ⋙ boundedToUnboundedEnhanced X ≅
      boundedToUnboundedEnhanced X ⋙ quotientTranslation X c :=
  Localization.liftNatIso
    (boundedGeneratedQuotientFunctor X) (BoundedGeneratedNegligible X).trW
    (boundedGeneratedQuotientFunctor X ⋙
      (boundedQuotientTranslation X c ⋙ boundedToUnboundedEnhanced X))
    (boundedGeneratedQuotientFunctor X ⋙
      (boundedToUnboundedEnhanced X ⋙ quotientTranslation X c))
    (boundedQuotientTranslation X c ⋙ boundedToUnboundedEnhanced X)
    (boundedToUnboundedEnhanced X ⋙ quotientTranslation X c)
    (boundedToUnboundedEnhancedTranslationPrequotientIso X c)

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
