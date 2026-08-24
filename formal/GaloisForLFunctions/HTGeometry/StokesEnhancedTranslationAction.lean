import GaloisForLFunctions.HTGeometry.StokesBoundedEnhancedTranslationPullback
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Additive action of enhanced translation pullback

Enhanced translation pullback respects zero and addition on small compact-support models,
ind-sheaves, derived categories, and both generated enhanced Verdier quotients. These are the
identity and composition coherence isomorphisms underlying the real translation action.
-/

open CategoryTheory CategoryTheory.Limits

namespace GaloisForLFunctions.IrregularStokes.EnhancedTranslation

open CompactIndSheaf EnhancedIndPullback Bordered

/-- Equal proper maps induce isomorphic pullback functors on universe-small compact-support
models. -/
noncomputable def smallProperPullbackEqIso {X Y : TopCat.{0}}
    {f g : X ⟶ Y} (hf : IsProperMap f) (hg : IsProperMap g) (h : f = g) :
    smallProperPullback f hf ≅ smallProperPullback g hg := by
  subst g
  rfl

/-- Proper pullback by the identity is the identity on universe-small compact-support models. -/
noncomputable def smallProperPullbackIdIso (X : TopCat.{0}) :
    smallProperPullback (𝟙 X) isProperMap_id ≅
      𝟭 (SmallCompactlySupportedSheaf X) := by
  let eX : CompactlySupportedSheaf X ≌ SmallCompactlySupportedSheaf X := AsSmall.equiv
  change eX.inverse ⋙
      (properPullback (𝟙 X) isProperMap_id ⋙ eX.functor) ≅ 𝟭 _
  exact Functor.isoWhiskerLeft eX.inverse
      (Functor.isoWhiskerRight (properPullbackIdIso X) eX.functor ≪≫
        Functor.leftUnitor eX.functor) ≪≫
    eX.counitIso

/-- Translation by zero pulls back as the identity on small compact-support models. -/
noncomputable def smallTranslationZeroIso (X : TopCat.{0}) :
    smallTranslationPullback X 0 ≅
      𝟭 (SmallCompactlySupportedSheaf (EnhancedCompactification X)) := by
  exact smallProperPullbackEqIso (enhancedTranslation_isProper X 0) isProperMap_id
      (enhancedTranslation_zero X) ≪≫
    smallProperPullbackIdIso (EnhancedCompactification X)

/-- Successive small-model translation pullbacks add their translation parameters. -/
noncomputable def smallTranslationCompIso (X : TopCat.{0}) (c d : ℝ) :
    smallTranslationPullback X c ⋙ smallTranslationPullback X d ≅
      smallTranslationPullback X (c + d) := by
  simpa only [enhancedTranslation_comp, add_comm] using
    smallProperPullbackCompIso (enhancedTranslation X d) (enhancedTranslation X c)
      (enhancedTranslation_isProper X d) (enhancedTranslation_isProper X c)

/-- Translation by zero pulls back as the identity on ind-sheaves. -/
noncomputable def indTranslationZeroIso (X : TopCat.{0}) :
    indTranslationPullback X 0 ≅ 𝟭 (IndSheaf (EnhancedCompactification X)) :=
  CategoryTheory.Ind.mapNatIso (smallTranslationZeroIso X) ≪≫
    CategoryTheory.Ind.mapIdIso

/-- Successive ind-sheaf translation pullbacks add their translation parameters. -/
noncomputable def indTranslationCompIso (X : TopCat.{0}) (c d : ℝ) :
    indTranslationPullback X c ⋙ indTranslationPullback X d ≅
      indTranslationPullback X (c + d) :=
  CategoryTheory.Ind.mapCompIso (smallTranslationPullback X c)
      (smallTranslationPullback X d) ≪≫
    CategoryTheory.Ind.mapNatIso (smallTranslationCompIso X c d)

/-- Translation by zero pulls back as the identity on unbounded derived ind-sheaves. -/
noncomputable def derivedTranslationZeroIso (X : TopCat.{0}) :
    derivedTranslationPullback X 0 ≅
      𝟭 (DerivedIndSheaf (EnhancedCompactification X)) :=
  Functor.mapDerivedCategoryNatIso (indTranslationZeroIso X) ≪≫
    Functor.mapDerivedCategoryIdIso

/-- Successive derived translation pullbacks add their translation parameters. -/
noncomputable def derivedTranslationCompIso (X : TopCat.{0}) (c d : ℝ) :
    derivedTranslationPullback X c ⋙ derivedTranslationPullback X d ≅
      derivedTranslationPullback X (c + d) := by
  letI : PreservesFiniteLimits
      (indTranslationPullback X c ⋙ indTranslationPullback X d) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (indTranslationPullback X c ⋙ indTranslationPullback X d) :=
    comp_preservesFiniteColimits _ _
  exact Functor.mapDerivedCategoryCompIso (indTranslationPullback X c)
      (indTranslationPullback X d) ≪≫
    Functor.mapDerivedCategoryNatIso (indTranslationCompIso X c d)

/-- Translation by zero pulls back as the identity on bounded derived ind-sheaves. -/
noncomputable def boundedDerivedTranslationZeroIso (X : TopCat.{0}) :
    boundedDerivedTranslationPullback X 0 ≅
      𝟭 (BoundedDerivedIndSheaf (EnhancedCompactification X)) :=
  Functor.fullyFaithfulCancelRight
    (DerivedCategory.Bounded.ι (C := IndSheaf (EnhancedCompactification X)))
    (boundedDerivedTranslationPullbackCompInclusionIso X 0 ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι
        (derivedTranslationZeroIso X) ≪≫
      Functor.rightUnitor DerivedCategory.Bounded.ι ≪≫
      (Functor.leftUnitor DerivedCategory.Bounded.ι).symm)

/-- Successive bounded-derived translation pullbacks add their parameters. -/
noncomputable def boundedDerivedTranslationCompIso
    (X : TopCat.{0}) (c d : ℝ) :
    boundedDerivedTranslationPullback X c ⋙ boundedDerivedTranslationPullback X d ≅
      boundedDerivedTranslationPullback X (c + d) :=
  Functor.fullyFaithfulCancelRight
    (DerivedCategory.Bounded.ι (C := IndSheaf (EnhancedCompactification X)))
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedDerivedTranslationPullbackCompInclusionIso X d) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedDerivedTranslationPullbackCompInclusionIso X c)
        (derivedTranslationPullback X d) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedTranslationCompIso X c d) ≪≫
      (boundedDerivedTranslationPullbackCompInclusionIso X (c + d)).symm)

/-- Translation by zero is the identity on the unbounded generated enhanced quotient. -/
noncomputable def quotientTranslationZeroIso (X : TopCat.{0}) :
    quotientTranslation X 0 ≅ 𝟭 (GeneratedEnhancedQuotient X) := by
  let Q := generatedQuotientFunctor X
  let T := derivedTranslationPullback X 0
  let QT := quotientTranslation X 0
  letI : Localization.Lifting Q (GeneratedNegligible X).trW (T ⋙ Q) QT :=
    ⟨(quotientTranslationSquare X 0).symm⟩
  exact Localization.liftNatIso Q (GeneratedNegligible X).trW
    (T ⋙ Q) Q QT (𝟭 (GeneratedEnhancedQuotient X))
    (Functor.isoWhiskerRight (derivedTranslationZeroIso X) Q ≪≫
      Functor.leftUnitor Q)

/-- Successive translations on the unbounded enhanced quotient add their parameters. -/
noncomputable def quotientTranslationCompIso (X : TopCat.{0}) (c d : ℝ) :
    quotientTranslation X c ⋙ quotientTranslation X d ≅
      quotientTranslation X (c + d) := by
  let Q := generatedQuotientFunctor X
  let Tc := derivedTranslationPullback X c
  let Td := derivedTranslationPullback X d
  let Tcd := derivedTranslationPullback X (c + d)
  let Qc := quotientTranslation X c
  let Qd := quotientTranslation X d
  let Qcd := quotientTranslation X (c + d)
  letI : Localization.Lifting Q (GeneratedNegligible X).trW
      ((Tc ⋙ Td) ⋙ Q) (Qc ⋙ Qd) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (quotientTranslationSquare X c).symm Qd ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Tc (quotientTranslationSquare X d).symm ≪≫
      (Functor.associator _ _ _).symm⟩
  letI : Localization.Lifting Q (GeneratedNegligible X).trW
      (Tcd ⋙ Q) Qcd :=
    ⟨(quotientTranslationSquare X (c + d)).symm⟩
  exact Localization.liftNatIso Q (GeneratedNegligible X).trW
    ((Tc ⋙ Td) ⋙ Q) (Tcd ⋙ Q) (Qc ⋙ Qd) Qcd
    (Functor.isoWhiskerRight (derivedTranslationCompIso X c d) Q)

/-- Translation by zero is the identity on the bounded generated enhanced quotient. -/
noncomputable def boundedQuotientTranslationZeroIso (X : TopCat.{0}) :
    boundedQuotientTranslation X 0 ≅
      𝟭 (BoundedGeneratedEnhancedQuotient X) := by
  let Q := boundedGeneratedQuotientFunctor X
  let T := boundedDerivedTranslationPullback X 0
  let QT := boundedQuotientTranslation X 0
  letI : Localization.Lifting Q (BoundedGeneratedNegligible X).trW (T ⋙ Q) QT :=
    ⟨(boundedQuotientTranslationSquare X 0).symm⟩
  exact Localization.liftNatIso Q (BoundedGeneratedNegligible X).trW
    (T ⋙ Q) Q QT (𝟭 (BoundedGeneratedEnhancedQuotient X))
    (Functor.isoWhiskerRight (boundedDerivedTranslationZeroIso X) Q ≪≫
      Functor.leftUnitor Q)

/-- Successive translations on the bounded enhanced quotient add their parameters. -/
noncomputable def boundedQuotientTranslationCompIso
    (X : TopCat.{0}) (c d : ℝ) :
    boundedQuotientTranslation X c ⋙ boundedQuotientTranslation X d ≅
      boundedQuotientTranslation X (c + d) := by
  let Q := boundedGeneratedQuotientFunctor X
  let Tc := boundedDerivedTranslationPullback X c
  let Td := boundedDerivedTranslationPullback X d
  let Tcd := boundedDerivedTranslationPullback X (c + d)
  let Qc := boundedQuotientTranslation X c
  let Qd := boundedQuotientTranslation X d
  let Qcd := boundedQuotientTranslation X (c + d)
  letI : Localization.Lifting Q (BoundedGeneratedNegligible X).trW
      ((Tc ⋙ Td) ⋙ Q) (Qc ⋙ Qd) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedQuotientTranslationSquare X c).symm Qd ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Tc (boundedQuotientTranslationSquare X d).symm ≪≫
      (Functor.associator _ _ _).symm⟩
  letI : Localization.Lifting Q (BoundedGeneratedNegligible X).trW
      (Tcd ⋙ Q) Qcd :=
    ⟨(boundedQuotientTranslationSquare X (c + d)).symm⟩
  exact Localization.liftNatIso Q (BoundedGeneratedNegligible X).trW
    ((Tc ⋙ Td) ⋙ Q) (Tcd ⋙ Q) (Qc ⋙ Qd) Qcd
    (Functor.isoWhiskerRight (boundedDerivedTranslationCompIso X c d) Q)

end GaloisForLFunctions.IrregularStokes.EnhancedTranslation
