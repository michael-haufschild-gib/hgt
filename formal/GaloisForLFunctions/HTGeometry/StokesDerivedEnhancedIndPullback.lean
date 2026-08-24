import GaloisForLFunctions.HTGeometry.StokesEnhancedIndProjectionPullbackExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived enhanced pullback on ind-sheaves

Exact enhanced-projection pullback induces a functor on unbounded derived categories. Mathlib's
exact-functor construction supplies its comparison with degreewise pullback, compatibility with
all integer shifts, and triangulatedness.
-/

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CategoryTheory
open CompactIndSheaf

/-- Standard chosen unbounded derived category of compactly generated ind-sheaves. -/
noncomputable instance indSheaf_hasDerivedCategory (X : TopCat.{0}) :
    HasDerivedCategory (IndSheaf X) :=
  HasDerivedCategory.standard (IndSheaf X)

/-- Unbounded derived category of compactly generated ind-sheaves. -/
abbrev DerivedIndSheaf (X : TopCat.{0}) := DerivedCategory (IndSheaf X)

/-- Derived enhanced-projection pullback on unbounded derived categories of ind-sheaves. -/
noncomputable def derivedEnhancedIndProjectionPullback (X : TopCat.{0}) :
    DerivedIndSheaf X ⥤ DerivedIndSheaf (EnhancedCompactification X) :=
  (enhancedIndProjectionPullback X).mapDerivedCategory

/-- Derived enhanced pullback is induced by degreewise pullback on unbounded cochain complexes. -/
noncomputable def derivedEnhancedIndProjectionPullbackFactors (X : TopCat.{0}) :
    DerivedCategory.Q ⋙ derivedEnhancedIndProjectionPullback X ≅
      (enhancedIndProjectionPullback X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (enhancedIndProjectionPullback X).mapDerivedCategoryFactors

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
