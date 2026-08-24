import GaloisForLFunctions.HTGeometry.StokesEnhancedTranslationAction

/-!
# Enhanced translation autoequivalences

Translation by `c` is inverse, up to the established zero and composition isomorphisms, to
translation by `-c`. This packages finite enhanced translations as autoequivalences at every
constructed categorical level.
-/

open CategoryTheory

namespace CategoryTheory.Functor

/-- Every functor family with zero and addition comparison isomorphisms acts by
autoequivalences. No associativity coherence equation is needed for this inverse construction. -/
noncomputable def additiveActionEquivalence {A C : Type*} [AddGroup A] [Category C]
    (T : A → C ⥤ C) (zeroIso : T 0 ≅ 𝟭 C)
    (compIso : ∀ a b, T a ⋙ T b ≅ T (a + b)) (a : A) : C ≌ C := by
  have hright : T a ⋙ T (-a) ≅ 𝟭 C := by
    exact compIso a (-a) ≪≫ eqToIso (congrArg T (add_neg_cancel a)) ≪≫ zeroIso
  have hleft : T (-a) ⋙ T a ≅ 𝟭 C := by
    exact compIso (-a) a ≪≫ eqToIso (congrArg T (neg_add_cancel a)) ≪≫ zeroIso
  exact Equivalence.mk (T a) (T (-a)) hright.symm hleft

end CategoryTheory.Functor

namespace GaloisForLFunctions.IrregularStokes.EnhancedTranslation

open CompactIndSheaf EnhancedIndPullback Bordered

/-- Equal proper maps induce isomorphic pullback functors on compactly supported sheaves. -/
noncomputable def properPullbackEqIso {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (hf : IsProperMap f) (hg : IsProperMap g) (h : f = g) :
    properPullback f hf ≅ properPullback g hg := by
  subst g
  rfl

/-- Translation by zero pulls back as the identity on compactly supported sheaves. -/
noncomputable def translationZeroIso (X : TopCat.{0}) :
    translationPullback X 0 ≅
      𝟭 (CompactlySupportedSheaf (EnhancedCompactification X)) :=
  properPullbackEqIso (enhancedTranslation_isProper X 0) isProperMap_id
      (enhancedTranslation_zero X) ≪≫
    properPullbackIdIso (EnhancedCompactification X)

/-- Successive compact-support translation pullbacks add their translation parameters. -/
noncomputable def translationCompIso (X : TopCat.{0}) (c d : ℝ) :
    translationPullback X c ⋙ translationPullback X d ≅
      translationPullback X (c + d) := by
  simpa only [translationPullback, enhancedTranslation_comp, add_comm] using
    properPullbackCompIso (enhancedTranslation X d) (enhancedTranslation X c)
      (enhancedTranslation_isProper X d) (enhancedTranslation_isProper X c)

/-- Finite enhanced translation is an autoequivalence on compactly supported sheaves. -/
noncomputable def translationEquivalence (X : TopCat.{0}) (c : ℝ) :
    CompactlySupportedSheaf (EnhancedCompactification X) ≌
      CompactlySupportedSheaf (EnhancedCompactification X) :=
  CategoryTheory.Functor.additiveActionEquivalence
    (fun d : ℝ => translationPullback X d)
    (translationZeroIso X) (translationCompIso X) c

/-- Finite enhanced translation is an autoequivalence on small compact-support models. -/
noncomputable def smallTranslationEquivalence (X : TopCat.{0}) (c : ℝ) :
    SmallCompactlySupportedSheaf (EnhancedCompactification X) ≌
      SmallCompactlySupportedSheaf (EnhancedCompactification X) :=
  CategoryTheory.Functor.additiveActionEquivalence
    (fun d : ℝ => smallTranslationPullback X d)
    (smallTranslationZeroIso X) (smallTranslationCompIso X) c

/-- Finite enhanced translation is an autoequivalence on ind-sheaves. -/
noncomputable def indTranslationEquivalence (X : TopCat.{0}) (c : ℝ) :
    IndSheaf (EnhancedCompactification X) ≌ IndSheaf (EnhancedCompactification X) :=
  CategoryTheory.Functor.additiveActionEquivalence
    (fun d : ℝ => indTranslationPullback X d)
    (indTranslationZeroIso X) (indTranslationCompIso X) c

/-- Finite enhanced translation is an autoequivalence on unbounded derived ind-sheaves. -/
noncomputable def derivedTranslationEquivalence (X : TopCat.{0}) (c : ℝ) :
    DerivedIndSheaf (EnhancedCompactification X) ≌
      DerivedIndSheaf (EnhancedCompactification X) :=
  CategoryTheory.Functor.additiveActionEquivalence
    (fun d : ℝ => derivedTranslationPullback X d)
    (derivedTranslationZeroIso X) (derivedTranslationCompIso X) c

/-- Finite enhanced translation is an autoequivalence on bounded derived ind-sheaves. -/
noncomputable def boundedDerivedTranslationEquivalence (X : TopCat.{0}) (c : ℝ) :
    BoundedDerivedIndSheaf (EnhancedCompactification X) ≌
      BoundedDerivedIndSheaf (EnhancedCompactification X) :=
  CategoryTheory.Functor.additiveActionEquivalence
    (fun d : ℝ => boundedDerivedTranslationPullback X d)
    (boundedDerivedTranslationZeroIso X) (boundedDerivedTranslationCompIso X) c

/-- Finite enhanced translation is an autoequivalence on the unbounded generated quotient. -/
noncomputable def quotientTranslationEquivalence (X : TopCat.{0}) (c : ℝ) :
    GeneratedEnhancedQuotient X ≌ GeneratedEnhancedQuotient X :=
  CategoryTheory.Functor.additiveActionEquivalence
    (fun d : ℝ => quotientTranslation X d)
    (quotientTranslationZeroIso X) (quotientTranslationCompIso X) c

/-- Finite enhanced translation is an autoequivalence on the bounded generated quotient. -/
noncomputable def boundedQuotientTranslationEquivalence (X : TopCat.{0}) (c : ℝ) :
    BoundedGeneratedEnhancedQuotient X ≌ BoundedGeneratedEnhancedQuotient X :=
  CategoryTheory.Functor.additiveActionEquivalence
    (fun d : ℝ => boundedQuotientTranslation X d)
    (boundedQuotientTranslationZeroIso X) (boundedQuotientTranslationCompIso X) c

end GaloisForLFunctions.IrregularStokes.EnhancedTranslation
