import GaloisForLFunctions.HTGeometry.StokesOrdinaryEpigraphConvolution
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Derived direct image on exponential epigraphs

For universe-zero sheaves of integer modules, inverse image preserves finite limits. Hence direct
image preserves injective objects and admits a bounded-below right-derived functor. Specializing to
proper fiberwise epigraph addition gives the direct-image half of derived convolution.

This file does not construct derived tensor, proper-support direct image for nonproper maps,
enhanced sheaves, or irregular Riemann--Hilbert correspondence.
-/

namespace GaloisForLFunctions.IrregularStokes.DerivedDirectImage

open CategoryTheory Limits
open OrdinaryConvolution

local instance intModuleForgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget (IntModuleCat.{0})) :=
  ModuleCat.FilteredColimits.forget_preservesFilteredColimits

set_option maxHeartbeats 1000000 in
attribute [local instance] CategoryTheory.Limits.reflectsLimits_of_reflectsIsomorphisms in
/-- Pullback of universe-zero integer-module sheaves preserves finite limits. -/
noncomputable instance intModuleSheafPullback_preservesFiniteLimits
    {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (IntModuleCat.{0}) f) := by
  unfold TopCat.Sheaf.pullback
  apply CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- Direct image of universe-zero integer-module sheaves is additive. -/
instance intModuleSheafPushforward_additive {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    (TopCat.Sheaf.pushforward (IntModuleCat.{0}) f).Additive where
  map_add {A B} α β := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    rfl

/-- Direct image of universe-zero integer-module sheaves preserves injective objects. -/
instance intModuleSheafPushforward_preservesInjectiveObjects
    {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    (TopCat.Sheaf.pushforward (IntModuleCat.{0}) f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction (IntModuleCat.{0}) f)

/-- The standard bounded-below derived category of integer-module sheaves exists. -/
theorem intModuleSheaf_hasDerivedCategory (Y : TopCat.{0}) :
    Nonempty (HasDerivedCategory.{1} (TopCat.Sheaf (IntModuleCat.{0}) Y)) :=
  ⟨HasDerivedCategory.standard _⟩

noncomputable local instance intModuleSheafHasDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory.{1} (TopCat.Sheaf (IntModuleCat.{0}) Y) :=
  HasDerivedCategory.standard _

/-- Bounded-below right-derived direct image for integer-module sheaves. -/
noncomputable def rightDerivedSheafPushforward {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    DerivedCategory.Plus (TopCat.Sheaf (IntModuleCat.{0}) Y) ⥤
      DerivedCategory.Plus (TopCat.Sheaf (IntModuleCat.{0}) Z) :=
  (TopCat.Sheaf.pushforward (IntModuleCat.{0}) f).rightDerivedFunctorPlus

/-- Right-derived direct image exposed with a properness certificate. This is not a construction
of proper-support direct image for nonproper maps. -/
noncomputable def rightDerivedProperPushforward {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (_hf : IsProperMap f) :
    DerivedCategory.Plus (TopCat.Sheaf (IntModuleCat.{0}) Y) ⥤
      DerivedCategory.Plus (TopCat.Sheaf (IntModuleCat.{0}) Z) :=
  rightDerivedSheafPushforward f

variable {X : Type} [TopologicalSpace X]

/-- Bounded-below right-derived direct image along proper exponential-epigraph addition. -/
noncomputable def derivedEpigraphPushforwardFunctor (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    DerivedCategory.Plus
        (TopCat.Sheaf (IntModuleCat.{0})
          (TopCat.of (ProperEpigraphAddition.exponentialEpigraphPair φ ψ))) ⥤
      DerivedCategory.Plus
        (TopCat.Sheaf (IntModuleCat.{0})
          (TopCat.of (EnhancedEpigraph.exponentialEpigraph
            (fun x => φ x + ψ x)))) :=
  rightDerivedProperPushforward
    (OrdinaryConvolution.epigraphFiberwiseAdditionHom φ ψ hφ hψ)
    (OrdinaryConvolution.epigraphFiberwiseAdditionHom_isProperMap φ ψ hφ hψ)

end GaloisForLFunctions.IrregularStokes.DerivedDirectImage
