import GaloisForLFunctions.HTGeometry.StokesSheafHomeomorph
import GaloisForLFunctions.HTGeometry.StokesEnhancedExponentialObject

/-!
# Translation covariance of enhanced exponential objects

Compactified exponential epigraph sheaves are covariant under translation of the enhanced real
variable: inverse image by translation through `c` subtracts `c` from the phase. The comparison is
lifted from ordinary sheaves through compact support, ind-sheaves, unbounded and bounded derived
categories, and both generated enhanced Verdier quotients.
-/

open CategoryTheory CategoryTheory.Limits Topology

namespace GaloisForLFunctions.IrregularStokes.EnhancedExponentialTranslation

open CompactIndSheaf CompactIndEmbedding EnhancedIndPullback Bordered
open OrdinaryConvolution ClosedSupportSheaf EnhancedExponential
open EnhancedTranslation SheafHomeomorph

/-- Topological isomorphism induced by compactified enhanced translation. -/
noncomputable def enhancedTranslationIso (X : TopCat.{0}) (c : ℝ) :
    EnhancedCompactification X ≅ EnhancedCompactification X :=
  TopCat.isoOfHomeo (enhancedTranslationHomeomorph X c)

@[simp]
theorem enhancedTranslationIso_hom (X : TopCat.{0}) (c : ℝ) :
    (enhancedTranslationIso X c).hom = enhancedTranslation X c := by
  rfl

/-- Translation by `c` identifies the epigraph of `φ - c` with the epigraph of `φ`. -/
noncomputable def compactifiedEpigraphTranslationIso
    (X : TopCat.{0}) (φ : X → ℝ) (c : ℝ) :
    TopCat.of (compactifiedExponentialEpigraph (fun x => φ x - c)) ≅
      TopCat.of (compactifiedExponentialEpigraph φ) :=
  TopCat.isoOfHomeo ((enhancedTranslationHomeomorph X c).subtype fun p =>
    (Set.ext_iff.mp
      (enhancedTranslation_preimage_compactifiedExponentialEpigraph X φ c) p).symm)

/-- The inverse support isomorphism followed by inclusion is translated ambient inclusion. -/
theorem compactifiedEpigraphTranslationIso_inv_comp
    (X : TopCat.{0}) (φ : X → ℝ) (c : ℝ) :
    (compactifiedEpigraphTranslationIso X φ c).inv ≫
        subtypeInclusion (compactifiedExponentialEpigraph (fun x => φ x - c)) =
      subtypeInclusion (compactifiedExponentialEpigraph φ) ≫
        enhancedTranslation X (-c) := by
  ext p
  · rfl
  · change p.1.2 + (-c : ℝ) = p.1.2 + (-c : ℝ)
    rfl

/-- Ordinary compactified exponential sheaves transform by phase subtraction. -/
noncomputable def compactifiedExponentialSheafTranslationIso
    (X : TopCat.{0}) (φ : X → ℝ) (hφ : Continuous φ) (c : ℝ) :
    (TopCat.Sheaf.pullback IntModuleCat (enhancedTranslation X c)).obj
        (compactifiedExponentialSheaf X φ hφ) ≅
      compactifiedExponentialSheaf X (fun x => φ x - c)
        (hφ.sub continuous_const) := by
  let S := compactifiedExponentialEpigraph φ
  let S' := compactifiedExponentialEpigraph (fun x => φ x - c)
  let Hs := compactifiedEpigraphTranslationIso X φ c
  let A : IntModuleCat := ModuleCat.of ℤ ℤ
  exact
    (sheafPullbackIsoPushforwardInv (enhancedTranslationIso X c)).app
        (compactifiedExponentialSheaf X φ hφ) ≪≫
      (sheafPushforwardCompIso (subtypeInclusion S)
        (enhancedTranslation X (-c))).symm.app
          (constantIntModuleSheaf (TopCat.of S) A) ≪≫
      (sheafPushforwardEqIso
        (compactifiedEpigraphTranslationIso_inv_comp X φ c).symm).app
          (constantIntModuleSheaf (TopCat.of S) A) ≪≫
      (sheafPushforwardCompIso Hs.inv (subtypeInclusion S')).app
          (constantIntModuleSheaf (TopCat.of S) A) ≪≫
      (TopCat.Sheaf.pushforward IntModuleCat (subtypeInclusion S')).mapIso
        ((constantSheafPushforwardIso Hs.symm).app A)

/-- Compact-support exponential sheaves transform by phase subtraction. -/
noncomputable def compactifiedExponentialCompactSheafTranslationIso
    (X : TopCat.{0}) [CompactSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) (c : ℝ) :
    (translationPullback X c).obj (compactifiedExponentialCompactSheaf X φ hφ) ≅
      compactifiedExponentialCompactSheaf X (fun x => φ x - c)
        (hφ.sub continuous_const) :=
  ObjectProperty.isoMk (HasCompactSupport (EnhancedCompactification X))
    (compactifiedExponentialSheafTranslationIso X φ hφ c)

/-- Transport to the universe-small compact-support model commutes with translation pullback. -/
noncomputable def compactToSmallCompSmallTranslationPullbackIso
    (X : TopCat.{0}) (c : ℝ) :
    (AsSmall.equiv : CompactlySupportedSheaf (EnhancedCompactification X) ≌
        SmallCompactlySupportedSheaf (EnhancedCompactification X)).functor ⋙
      smallTranslationPullback X c ≅
    translationPullback X c ⋙
      (AsSmall.equiv : CompactlySupportedSheaf (EnhancedCompactification X) ≌
        SmallCompactlySupportedSheaf (EnhancedCompactification X)).functor := by
  let e : CompactlySupportedSheaf (EnhancedCompactification X) ≌
      SmallCompactlySupportedSheaf (EnhancedCompactification X) := AsSmall.equiv
  let F := translationPullback X c
  change e.functor ⋙ (e.inverse ⋙ (F ⋙ e.functor)) ≅ F ⋙ e.functor
  exact (Functor.associator e.functor e.inverse (F ⋙ e.functor)).symm ≪≫
    Functor.isoWhiskerRight e.unitIso.symm (F ⋙ e.functor) ≪≫
    Functor.leftUnitor _

/-- Ind-translation agrees with proper translation pullback on representable compact sheaves. -/
noncomputable def indTranslationPullback_compactSheafIso
    (X : TopCat.{0}) (c : ℝ) :
    translationPullback X c ⋙
        compactSheafToIndSheaf (EnhancedCompactification X) ≅
      compactSheafToIndSheaf (EnhancedCompactification X) ⋙
        indTranslationPullback X c := by
  let e : CompactlySupportedSheaf (EnhancedCompactification X) ≌
      SmallCompactlySupportedSheaf (EnhancedCompactification X) := AsSmall.equiv
  let F := translationPullback X c
  let Fs := smallTranslationPullback X c
  let y : SmallCompactlySupportedSheaf (EnhancedCompactification X) ⥤
      IndSheaf (EnhancedCompactification X) := CategoryTheory.Ind.yoneda
  change F ⋙ (e.functor ⋙ y) ≅ (e.functor ⋙ y) ⋙ CategoryTheory.Ind.map Fs
  exact (Functor.associator F e.functor y).symm ≪≫
    Functor.isoWhiskerRight
      (compactToSmallCompSmallTranslationPullbackIso X c).symm y ≪≫
    Functor.associator e.functor Fs y ≪≫
    Functor.isoWhiskerLeft e.functor (CategoryTheory.Ind.mapYonedaIso Fs) ≪≫
    (Functor.associator e.functor y (CategoryTheory.Ind.map Fs)).symm

/-- Ind-sheaf exponential objects transform by phase subtraction. -/
noncomputable def compactifiedExponentialIndSheafTranslationIso
    (X : TopCat.{0}) [CompactSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) (c : ℝ) :
    (indTranslationPullback X c).obj (compactifiedExponentialIndSheaf X φ hφ) ≅
      compactifiedExponentialIndSheaf X (fun x => φ x - c)
        (hφ.sub continuous_const) :=
  (indTranslationPullback_compactSheafIso X c).symm.app
      (compactifiedExponentialCompactSheaf X φ hφ) ≪≫
    (compactSheafToIndSheaf (EnhancedCompactification X)).mapIso
      (compactifiedExponentialCompactSheafTranslationIso X φ hφ c)

/-- Unbounded derived exponential objects transform by phase subtraction. -/
noncomputable def compactifiedExponentialDerivedTranslationIso
    (X : TopCat.{0}) [CompactSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) (c : ℝ) :
    (derivedTranslationPullback X c).obj
        (compactifiedExponentialDerivedObject X φ hφ) ≅
      compactifiedExponentialDerivedObject X (fun x => φ x - c)
        (hφ.sub continuous_const) :=
  (CategoryTheory.Functor.mapDerivedCategorySingleFunctor
      (indTranslationPullback X c) 0).app
        (compactifiedExponentialIndSheaf X φ hφ) ≪≫
    (DerivedCategory.singleFunctor (IndSheaf (EnhancedCompactification X)) 0).mapIso
      (compactifiedExponentialIndSheafTranslationIso X φ hφ c)

/-- Bounded derived exponential objects transform by phase subtraction. -/
noncomputable def compactifiedExponentialBoundedDerivedTranslationIso
    (X : TopCat.{0}) [CompactSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) (c : ℝ) :
    (boundedDerivedTranslationPullback X c).obj
        (compactifiedExponentialBoundedDerivedObject X φ hφ) ≅
      compactifiedExponentialBoundedDerivedObject X (fun x => φ x - c)
        (hφ.sub continuous_const) :=
  ObjectProperty.isoMk DerivedCategory.TStructure.t.bounded
    (compactifiedExponentialDerivedTranslationIso X φ hφ c)

/-- Unbounded generated enhanced exponential objects transform by phase subtraction. -/
noncomputable def compactifiedExponentialEnhancedTranslationIso
    (X : TopCat.{0}) [CompactSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) (c : ℝ) :
    (quotientTranslation X c).obj
        (compactifiedExponentialEnhancedObject X φ hφ) ≅
      compactifiedExponentialEnhancedObject X (fun x => φ x - c)
        (hφ.sub continuous_const) :=
  (quotientTranslationSquare X c).symm.app
      (compactifiedExponentialDerivedObject X φ hφ) ≪≫
    (generatedQuotientFunctor X).mapIso
      (compactifiedExponentialDerivedTranslationIso X φ hφ c)

/-- Bounded generated enhanced exponential objects transform by phase subtraction. -/
noncomputable def compactifiedExponentialBoundedEnhancedTranslationIso
    (X : TopCat.{0}) [CompactSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) (c : ℝ) :
    (boundedQuotientTranslation X c).obj
        (compactifiedExponentialBoundedEnhancedObject X φ hφ) ≅
      compactifiedExponentialBoundedEnhancedObject X (fun x => φ x - c)
        (hφ.sub continuous_const) :=
  (boundedQuotientTranslationSquare X c).symm.app
      (compactifiedExponentialBoundedDerivedObject X φ hφ) ≪≫
    (boundedGeneratedQuotientFunctor X).mapIso
      (compactifiedExponentialBoundedDerivedTranslationIso X φ hφ c)

end GaloisForLFunctions.IrregularStokes.EnhancedExponentialTranslation
