import GaloisForLFunctions.HTGeometry.StokesProperPullbackExact
import Mathlib.Algebra.Homology.Localization

/-!
# Derived enhanced pullback on compact-support small models

Exact enhanced-projection pullback on universe-small compact-support sheaf models preserves
homology. Degreewise application therefore preserves quasi-isomorphisms and descends to the
quasi-isomorphism localizations of nonnegative complexes.

This is deliberately below the ind-extension: derived ind-sheaf pullback still requires exactness
of the chosen covariant ind-extension.
-/

namespace GaloisForLFunctions.IrregularStokes.EnhancedIndPullback

open CategoryTheory CategoryTheory.Limits
open CompactIndSheaf

noncomputable instance smallEnhancedProjectionPullback_additive (X : TopCat.{0}) :
    (smallEnhancedProjectionPullback X).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts
    (smallEnhancedProjectionPullback X)
  exact Functor.additive_of_preservesBinaryBiproducts _

noncomputable instance smallEnhancedProjectionPullback_preservesHomology (X : TopCat.{0}) :
    (smallEnhancedProjectionPullback X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

abbrev SmallCompactCC (X : TopCat.{0}) :=
  HomologicalComplex (SmallCompactlySupportedSheaf X) (ComplexShape.down ℕ)

abbrev SmallCompactW (X : TopCat.{0}) :=
  HomologicalComplex.quasiIso (SmallCompactlySupportedSheaf X) (ComplexShape.down ℕ)

abbrev DerivedSmallCompactCC (X : TopCat.{0}) :=
  (SmallCompactW X).Localization

/-- Degreewise enhanced-projection pullback on nonnegative complexes. -/
noncomputable def smallEnhancedProjectionPullbackComplex (X : TopCat.{0}) :
    CategoryTheory.Functor (SmallCompactCC X)
      (SmallCompactCC (EnhancedCompactification X)) :=
  (smallEnhancedProjectionPullback X).mapHomologicalComplex (ComplexShape.down ℕ)

theorem smallEnhancedProjectionPullbackComplex_map_quasiIso (X : TopCat.{0})
    {K L : SmallCompactCC X} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((smallEnhancedProjectionPullbackComplex X).map f) := by
  change QuasiIso (((smallEnhancedProjectionPullback X).mapHomologicalComplex
    (ComplexShape.down ℕ)).map f)
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f
    (smallEnhancedProjectionPullback X)

/-- Degreewise pullback followed by localization inverts source quasi-isomorphisms. -/
theorem smallEnhancedProjectionPullbackThenQ_inverts_quasiIso (X : TopCat.{0}) :
    (SmallCompactW X).IsInvertedBy
      (smallEnhancedProjectionPullbackComplex X ⋙
        (SmallCompactW (EnhancedCompactification X)).Q) := by
  intro K L f hf
  change QuasiIso f at hf
  letI : QuasiIso f := hf
  have hmap : SmallCompactW (EnhancedCompactification X)
      ((smallEnhancedProjectionPullbackComplex X).map f) := by
    change QuasiIso ((smallEnhancedProjectionPullbackComplex X).map f)
    exact smallEnhancedProjectionPullbackComplex_map_quasiIso X f
  exact Localization.inverts (SmallCompactW (EnhancedCompactification X)).Q
    (SmallCompactW (EnhancedCompactification X)) _ hmap

/-- Derived compact-support pullback along the enhanced projection. -/
noncomputable def derivedSmallEnhancedProjectionPullback (X : TopCat.{0}) :
    CategoryTheory.Functor (DerivedSmallCompactCC X)
      (DerivedSmallCompactCC (EnhancedCompactification X)) :=
  Localization.lift
    (smallEnhancedProjectionPullbackComplex X ⋙
      (SmallCompactW (EnhancedCompactification X)).Q)
    (smallEnhancedProjectionPullbackThenQ_inverts_quasiIso X)
    (SmallCompactW X).Q

/-- Derived pullback is induced by degreewise compact-support pullback. -/
noncomputable def derivedSmallEnhancedProjectionPullbackFactors (X : TopCat.{0}) :
    (SmallCompactW X).Q ⋙ derivedSmallEnhancedProjectionPullback X ≅
      smallEnhancedProjectionPullbackComplex X ⋙
        (SmallCompactW (EnhancedCompactification X)).Q :=
  Localization.fac _ (smallEnhancedProjectionPullbackThenQ_inverts_quasiIso X)
    (SmallCompactW X).Q

end GaloisForLFunctions.IrregularStokes.EnhancedIndPullback
