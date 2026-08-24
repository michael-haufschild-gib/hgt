import GaloisForLFunctions.HTGeometry.StokesIndFunctorExact
import GaloisForLFunctions.HTGeometry.StokesProperPullbackExact

/-!
# Exactness of enhanced-projection pullback on ind-sheaves

Exactness of proper pullback on universe-small compact-support models passes through covariant
ind-extension. Consequently enhanced-projection pullback on ind-sheaves preserves finite limits,
finite colimits, and homology.
-/

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CategoryTheory CategoryTheory.Limits
open CompactIndSheaf

/-- Enhanced-projection pullback on ind-sheaves preserves finite limits. -/
noncomputable instance enhancedIndProjectionPullback_preservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (enhancedIndProjectionPullback X) := by
  unfold enhancedIndProjectionPullback
  infer_instance

/-- Enhanced-projection pullback on ind-sheaves preserves finite colimits. -/
noncomputable instance enhancedIndProjectionPullback_preservesFiniteColimits (X : TopCat.{0}) :
    PreservesFiniteColimits (enhancedIndProjectionPullback X) := by
  unfold enhancedIndProjectionPullback
  infer_instance

/-- Enhanced-projection pullback on ind-sheaves is additive. -/
noncomputable instance enhancedIndProjectionPullback_additive (X : TopCat.{0}) :
    (enhancedIndProjectionPullback X).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts
    (enhancedIndProjectionPullback X)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Enhanced-projection pullback on ind-sheaves preserves homology. -/
noncomputable instance enhancedIndProjectionPullback_preservesHomology (X : TopCat.{0}) :
    (enhancedIndProjectionPullback X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
