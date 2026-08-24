import GaloisForLFunctions.HTGeometry.StokesERealTranslation
import GaloisForLFunctions.HTGeometry.StokesProperPullbackComposition
import GaloisForLFunctions.HTGeometry.StokesIndFunctoriality
import GaloisForLFunctions.HTGeometry.StokesIndFunctorExact
import GaloisForLFunctions.HTGeometry.StokesExactFunctorDerivedFunctoriality
import GaloisForLFunctions.HTGeometry.StokesGeneratedEnhancedVerdier
import GaloisForLFunctions.HTGeometry.StokesVerdierFunctorDescent

/-!
# Enhanced translation pullback

Proper translation in the compactified enhanced variable induces exact pullback on compactly
supported sheaves, small compact-support models, ind-sheaves, and derived ind-sheaves. Translation
preserves the projection-generated negligible subcategory and therefore descends to the generated
enhanced Verdier quotient.
-/

open CategoryTheory CategoryTheory.Limits

namespace GaloisForLFunctions.IrregularStokes.EnhancedTranslation

open CompactIndSheaf CompactIndEmbedding EnhancedIndPullback Bordered

/-- Pullback of compactly supported sheaves by a finite enhanced translation. -/
noncomputable def translationPullback (X : TopCat.{0}) (c : ℝ) :
    CompactlySupportedSheaf (EnhancedCompactification X) ⥤
      CompactlySupportedSheaf (EnhancedCompactification X) :=
  properPullback (enhancedTranslation X c) (enhancedTranslation_isProper X c)

/-- Proper pullback transported to universe-small compact-support models. -/
noncomputable def smallProperPullback {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) :
    SmallCompactlySupportedSheaf Y ⥤ SmallCompactlySupportedSheaf X :=
  (AsSmall.equiv : CompactlySupportedSheaf Y ≌ SmallCompactlySupportedSheaf Y).inverse ⋙
    (properPullback f hf ⋙
      (AsSmall.equiv : CompactlySupportedSheaf X ≌ SmallCompactlySupportedSheaf X).functor)

/-- Proper pullback on universe-small compact-support models composes contravariantly. -/
noncomputable def smallProperPullbackCompIso {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f) (hg : IsProperMap g) :
    smallProperPullback g hg ⋙ smallProperPullback f hf ≅
      smallProperPullback (f ≫ g) (by simpa using hg.comp hf) := by
  let eX : CompactlySupportedSheaf X ≌ SmallCompactlySupportedSheaf X := AsSmall.equiv
  let eY : CompactlySupportedSheaf Y ≌ SmallCompactlySupportedSheaf Y := AsSmall.equiv
  let eZ : CompactlySupportedSheaf Z ≌ SmallCompactlySupportedSheaf Z := AsSmall.equiv
  let Pf := properPullback f hf
  let Pg := properPullback g hg
  let Pfg := properPullback (f ≫ g) (by simpa using hg.comp hf)
  change (eZ.inverse ⋙ (Pg ⋙ eY.functor)) ⋙
      (eY.inverse ⋙ (Pf ⋙ eX.functor)) ≅ eZ.inverse ⋙ (Pfg ⋙ eX.functor)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft eZ.inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft Pg
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight eY.unitIso.symm (Pf ⋙ eX.functor) ≪≫
            Functor.leftUnitor _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (properPullbackCompIso f g hf hg) eX.functor)

/-- Enhanced translation pullback on universe-small compact-support models. -/
noncomputable abbrev smallTranslationPullback (X : TopCat.{0}) (c : ℝ) :
    SmallCompactlySupportedSheaf (EnhancedCompactification X) ⥤
      SmallCompactlySupportedSheaf (EnhancedCompactification X) :=
  smallProperPullback (enhancedTranslation X c) (enhancedTranslation_isProper X c)

/-- Projection pullback followed by translation pullback is projection pullback. -/
noncomputable def smallProjectionCompTranslationIso (X : TopCat.{0}) (c : ℝ) :
    smallEnhancedProjectionPullback X ⋙ smallTranslationPullback X c ≅
      smallEnhancedProjectionPullback X := by
  change smallProperPullback (enhancedProjection X) (enhancedProjection_isProper X) ⋙
      smallProperPullback (enhancedTranslation X c) (enhancedTranslation_isProper X c) ≅
    smallProperPullback (enhancedProjection X) (enhancedProjection_isProper X)
  simpa only [enhancedTranslation_comp_projection] using
    smallProperPullbackCompIso (enhancedTranslation X c) (enhancedProjection X)
      (enhancedTranslation_isProper X c) (enhancedProjection_isProper X)

/-- Enhanced translation pullback extended covariantly to ind-sheaves. -/
noncomputable def indTranslationPullback (X : TopCat.{0}) (c : ℝ) :
    IndSheaf (EnhancedCompactification X) ⥤ IndSheaf (EnhancedCompactification X) :=
  CategoryTheory.Ind.map (smallTranslationPullback X c)

noncomputable instance smallTranslationPullback_preservesFiniteLimits
    (X : TopCat.{0}) (c : ℝ) : PreservesFiniteLimits (smallTranslationPullback X c) := by
  dsimp [smallTranslationPullback, smallProperPullback]
  infer_instance

noncomputable instance smallTranslationPullback_preservesFiniteColimits
    (X : TopCat.{0}) (c : ℝ) : PreservesFiniteColimits (smallTranslationPullback X c) := by
  dsimp [smallTranslationPullback, smallProperPullback]
  infer_instance

noncomputable instance indTranslationPullback_preservesFiniteLimits
    (X : TopCat.{0}) (c : ℝ) : PreservesFiniteLimits (indTranslationPullback X c) := by
  unfold indTranslationPullback
  infer_instance

noncomputable instance indTranslationPullback_preservesFiniteColimits
    (X : TopCat.{0}) (c : ℝ) : PreservesFiniteColimits (indTranslationPullback X c) := by
  unfold indTranslationPullback
  infer_instance

noncomputable instance indTranslationPullback_additive (X : TopCat.{0}) (c : ℝ) :
    (indTranslationPullback X c).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts (indTranslationPullback X c)
  exact Functor.additive_of_preservesBinaryBiproducts _

noncomputable instance indTranslationPullback_preservesHomology (X : TopCat.{0}) (c : ℝ) :
    (indTranslationPullback X c).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Projection pullback followed by translation pullback is projection pullback on ind-sheaves. -/
noncomputable def indProjectionCompTranslationIso (X : TopCat.{0}) (c : ℝ) :
    enhancedIndProjectionPullback X ⋙ indTranslationPullback X c ≅
      enhancedIndProjectionPullback X :=
  CategoryTheory.Ind.mapCompIso (smallEnhancedProjectionPullback X)
      (smallTranslationPullback X c) ≪≫
    CategoryTheory.Ind.mapNatIso (smallProjectionCompTranslationIso X c)

/-- Derived pullback by finite translation of the enhanced variable. -/
noncomputable def derivedTranslationPullback (X : TopCat.{0}) (c : ℝ) :
    DerivedIndSheaf (EnhancedCompactification X) ⥤
      DerivedIndSheaf (EnhancedCompactification X) :=
  (indTranslationPullback X c).mapDerivedCategory

noncomputable instance derivedTranslationPullback_commShift (X : TopCat.{0}) (c : ℝ) :
    (derivedTranslationPullback X c).CommShift ℤ := by
  unfold derivedTranslationPullback
  infer_instance

noncomputable instance derivedTranslationPullback_isTriangulated (X : TopCat.{0}) (c : ℝ) :
    (derivedTranslationPullback X c).IsTriangulated := by
  unfold derivedTranslationPullback
  exact CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory
    (indTranslationPullback X c)

/-- Projection pullback followed by translation pullback is projection pullback after deriving. -/
noncomputable def derivedProjectionCompTranslationIso (X : TopCat.{0}) (c : ℝ) :
    derivedEnhancedIndProjectionPullback X ⋙ derivedTranslationPullback X c ≅
      derivedEnhancedIndProjectionPullback X := by
  letI : PreservesFiniteLimits
      (enhancedIndProjectionPullback X ⋙ indTranslationPullback X c) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (enhancedIndProjectionPullback X ⋙ indTranslationPullback X c) :=
    comp_preservesFiniteColimits _ _
  exact Functor.mapDerivedCategoryCompIso (enhancedIndProjectionPullback X)
      (indTranslationPullback X c) ≪≫
    Functor.mapDerivedCategoryNatIso (indProjectionCompTranslationIso X c)

/-- Derived enhanced translation preserves the thick envelope generated by base pullbacks. -/
theorem derivedTranslation_preservesGeneratedNegligible (X : TopCat.{0}) (c : ℝ) :
    GeneratedNegligible X ≤
      (GeneratedNegligible X).inverseImage (derivedTranslationPullback X c) := by
  letI : ((GeneratedNegligible X).inverseImage
      (derivedTranslationPullback X c)).IsStableUnderRetracts :=
    { of_retract := fun r h => (GeneratedNegligible X).prop_of_retract
        (r.map (derivedTranslationPullback X c)) h }
  rw [ObjectProperty.triangEnvelope_le_iff]
  rintro K ⟨L, ⟨e⟩⟩
  exact (GeneratedNegligible X).prop_of_iso
    ((derivedProjectionCompTranslationIso X c).symm.app L ≪≫
      (derivedTranslationPullback X c).mapIso e)
    ((DerivedProjectionImage X).le_triangEnvelope _ ⟨L, ⟨Iso.refl _⟩⟩)

/-- Finite enhanced translation descended to the generated unbounded enhanced quotient. -/
noncomputable abbrev quotientTranslation (X : TopCat.{0}) (c : ℝ) :
    GeneratedEnhancedQuotient X ⥤ GeneratedEnhancedQuotient X :=
  VerdierFunctor.mapVerdierQuotient (GeneratedNegligible X) (GeneratedNegligible X)
    (derivedTranslationPullback X c) (derivedTranslation_preservesGeneratedNegligible X c)

/-- Canonical square comparing derived and quotient-level enhanced translation. -/
noncomputable abbrev quotientTranslationSquare (X : TopCat.{0}) (c : ℝ) :
    derivedTranslationPullback X c ⋙ generatedQuotientFunctor X ≅
      generatedQuotientFunctor X ⋙ quotientTranslation X c :=
  VerdierFunctor.mapVerdierQuotientSquare (GeneratedNegligible X) (GeneratedNegligible X)
    (derivedTranslationPullback X c) (derivedTranslation_preservesGeneratedNegligible X c)

end GaloisForLFunctions.IrregularStokes.EnhancedTranslation
