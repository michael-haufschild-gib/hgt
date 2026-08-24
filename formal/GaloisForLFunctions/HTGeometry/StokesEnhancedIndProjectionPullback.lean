import GaloisForLFunctions.HTGeometry.StokesERealEnhancedProjection
import GaloisForLFunctions.HTGeometry.StokesIndFunctorExtension
import GaloisForLFunctions.HTGeometry.StokesCompactSheafToInd

/-!
# Enhanced-projection pullback on ind-sheaves

Proper pullback along `X × EReal ⟶ X` is transported to the universe-small compact-support models
and extended covariantly to ind-sheaves. The resulting functor agrees with ordinary proper pullback
on compact sheaves embedded as representable ind-objects.

Exactness and derived descent remain separate obligations.
-/

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CategoryTheory CategoryTheory.Functor
open CompactIndSheaf CompactIndEmbedding

/-- Proper enhanced-projection pullback transported to universe-small compact sheaves. -/
noncomputable def smallEnhancedProjectionPullback (X : TopCat.{0}) :
    SmallCompactlySupportedSheaf X ⥤
      SmallCompactlySupportedSheaf (EnhancedCompactification X) :=
  (AsSmall.equiv : CompactlySupportedSheaf X ≌
      SmallCompactlySupportedSheaf X).inverse ⋙
    (enhancedProjectionPullback X ⋙
      (AsSmall.equiv : CompactlySupportedSheaf (EnhancedCompactification X) ≌
        SmallCompactlySupportedSheaf (EnhancedCompactification X)).functor)

/-- Pullback along `X × EReal → X` extended covariantly to ind-sheaves. -/
noncomputable def enhancedIndProjectionPullback (X : TopCat.{0}) :
    IndSheaf X ⥤ IndSheaf (EnhancedCompactification X) :=
  CategoryTheory.Ind.map (smallEnhancedProjectionPullback X)

/-- Transporting small-model pullback back to compact sheaves recovers proper pullback. -/
noncomputable def compactToSmallCompSmallEnhancedProjectionPullbackIso (X : TopCat.{0}) :
    (AsSmall.equiv : CompactlySupportedSheaf X ≌
        SmallCompactlySupportedSheaf X).functor ⋙
      smallEnhancedProjectionPullback X ≅
    enhancedProjectionPullback X ⋙
      (AsSmall.equiv : CompactlySupportedSheaf (EnhancedCompactification X) ≌
        SmallCompactlySupportedSheaf (EnhancedCompactification X)).functor := by
  let eX : CompactlySupportedSheaf X ≌ SmallCompactlySupportedSheaf X := AsSmall.equiv
  let eE : CompactlySupportedSheaf (EnhancedCompactification X) ≌
      SmallCompactlySupportedSheaf (EnhancedCompactification X) := AsSmall.equiv
  change eX.functor ⋙ (eX.inverse ⋙ (enhancedProjectionPullback X ⋙ eE.functor)) ≅
    enhancedProjectionPullback X ⋙ eE.functor
  exact (Functor.associator eX.functor eX.inverse
      (enhancedProjectionPullback X ⋙ eE.functor)).symm ≪≫
    isoWhiskerRight eX.unitIso.symm (enhancedProjectionPullback X ⋙ eE.functor) ≪≫
    Functor.leftUnitor _

/-- On compact sheaves embedded as representable ind-objects, enhanced ind-pullback agrees with
ordinary proper pullback. -/
noncomputable def enhancedIndProjectionPullback_compactSheafIso (X : TopCat.{0}) :
    enhancedProjectionPullback X ⋙
        compactSheafToIndSheaf (EnhancedCompactification X) ≅
      compactSheafToIndSheaf X ⋙ enhancedIndProjectionPullback X := by
  let eX : CompactlySupportedSheaf X ≌ SmallCompactlySupportedSheaf X := AsSmall.equiv
  let eE : CompactlySupportedSheaf (EnhancedCompactification X) ≌
      SmallCompactlySupportedSheaf (EnhancedCompactification X) := AsSmall.equiv
  let F := enhancedProjectionPullback X
  let Fs := smallEnhancedProjectionPullback X
  let yX : SmallCompactlySupportedSheaf X ⥤ IndSheaf X := Ind.yoneda
  let yE : SmallCompactlySupportedSheaf (EnhancedCompactification X) ⥤
      IndSheaf (EnhancedCompactification X) := Ind.yoneda
  change F ⋙ (eE.functor ⋙ yE) ≅ (eX.functor ⋙ yX) ⋙ Ind.map Fs
  exact (Functor.associator F eE.functor yE).symm ≪≫
    isoWhiskerRight (compactToSmallCompSmallEnhancedProjectionPullbackIso X).symm yE ≪≫
    Functor.associator eX.functor Fs yE ≪≫
    isoWhiskerLeft eX.functor (Ind.mapYonedaIso Fs) ≪≫
    (Functor.associator eX.functor yX (Ind.map Fs)).symm

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
