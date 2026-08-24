import GaloisForLFunctions.HTGeometry.StokesEnhancedIndProjectionPullback
import GaloisForLFunctions.HTGeometry.StokesDerivedEpigraphDirectImage

/-!
# Exactness of proper pullback on compact-support models

Compact-support inclusions preserve kernels and cokernels, hence finite limits and colimits.
Ordinary sheaf pullback is left exact and a left adjoint. Restricting it along a proper map and
transporting it to universe-small compact-support models therefore preserves finite limits and
finite colimits.

Exactness of the subsequent ind-extension remains a separate theorem.
-/

namespace GaloisForLFunctions.IrregularStokes.CompactIndSheaf

open CategoryTheory CategoryTheory.Limits
open OrdinaryConvolution ExactSheafification

noncomputable instance hasCompactSupport_inclusion_preservesFiniteLimits (Y : TopCat.{0}) :
    PreservesFiniteLimits (HasCompactSupport Y).ι := by
  letI : ∀ {X Z : (HasCompactSupport Y).FullSubcategory} (f : X ⟶ Z),
      PreservesLimit (parallelPair f 0) (HasCompactSupport Y).ι :=
    fun f => (HasCompactSupport Y).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

noncomputable instance hasCompactSupport_inclusion_preservesFiniteColimits (Y : TopCat.{0}) :
    PreservesFiniteColimits (HasCompactSupport Y).ι := by
  letI : ∀ {X Z : (HasCompactSupport Y).FullSubcategory} (f : X ⟶ Z),
      PreservesColimit (parallelPair f 0) (HasCompactSupport Y).ι :=
    fun f => (HasCompactSupport Y).preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsProperMap f)

noncomputable instance properPullback_preservesFiniteLimits :
    PreservesFiniteLimits (properPullback f hf) := by
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback IntModuleCat.{0} f) :=
    DerivedDirectImage.intModuleSheafPullback_preservesFiniteLimits f
  letI : PreservesFiniteLimits
      (properPullback f hf ⋙ (HasCompactSupport X).ι) :=
    preservesFiniteLimits_of_natIso (properPullbackCompιIso f hf).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (properPullback f hf) (HasCompactSupport X).ι

noncomputable instance properPullback_preservesFiniteColimits :
    PreservesFiniteColimits (properPullback f hf) := by
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback IntModuleCat.{0} f) :=
    PreservesColimits.preservesFiniteColimits _
  letI : PreservesFiniteColimits
      (properPullback f hf ⋙ (HasCompactSupport X).ι) :=
    preservesFiniteColimits_of_natIso (properPullbackCompιIso f hf).symm
  exact preservesFiniteColimits_of_reflects_of_preserves
    (properPullback f hf) (HasCompactSupport X).ι

end GaloisForLFunctions.IrregularStokes.CompactIndSheaf

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CategoryTheory CategoryTheory.Limits
open CompactIndSheaf

noncomputable instance enhancedProjectionPullback_preservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (enhancedProjectionPullback X) := by
  unfold enhancedProjectionPullback
  infer_instance

noncomputable instance enhancedProjectionPullback_preservesFiniteColimits (X : TopCat.{0}) :
    PreservesFiniteColimits (enhancedProjectionPullback X) := by
  unfold enhancedProjectionPullback
  infer_instance

noncomputable instance smallEnhancedProjectionPullback_preservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (smallEnhancedProjectionPullback X) := by
  dsimp [smallEnhancedProjectionPullback]
  infer_instance

noncomputable instance smallEnhancedProjectionPullback_preservesFiniteColimits (X : TopCat.{0}) :
    PreservesFiniteColimits (smallEnhancedProjectionPullback X) := by
  dsimp [smallEnhancedProjectionPullback]
  infer_instance

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
