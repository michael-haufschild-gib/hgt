import GaloisForLFunctions.HTGeometry.StokesSymmetricMonoidalSheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Abelian

/-!
# Exact sheafification for integer-module complexes

On a universe-zero topological space, sheafification of integer-module presheaves preserves finite
limits and finite colimits, hence categorical homology and exact sequences. Its degreewise extension
therefore maps quasi-isomorphisms of nonnegative chain complexes to quasi-isomorphisms.

This does not prove exactness of sheaf tensor or K-flatness of a complex.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.IrregularStokes.ExactSheafification

open OrdinaryConvolution MonoidalSheafTensor

/-- Universe-zero integer modules admit left-exact sheafification on every universe-zero
topological space. The explicit universe annotation avoids an ambiguous larger module universe. -/
noncomputable instance intModuleHasSheafify (Y : TopCat.{0}) :
    HasSheafify (Opens.grothendieckTopology Y) (IntModuleCat.{0}) := by
  infer_instance

/-- Nonnegative chain complexes of integer-module presheaves. -/
abbrev IntModulePresheafChainComplex (Y : TopCat.{0}) :=
  ChainComplex (TopCat.Presheaf (IntModuleCat.{0}) Y) ℕ

/-- Nonnegative chain complexes of integer-module sheaves. -/
abbrev IntModuleSheafChainComplex (Y : TopCat.{0}) :=
  ChainComplex (TopCat.Sheaf (IntModuleCat.{0}) Y) ℕ

/-- Sheafification preserves finite limits. -/
noncomputable instance topPresheafToSheafPreservesFiniteLimits (Y : TopCat.{0}) :
    PreservesFiniteLimits (topPresheafToSheaf Y) := by
  change PreservesFiniteLimits
    (presheafToSheaf (Opens.grothendieckTopology Y) (IntModuleCat.{0}))
  infer_instance

/-- Sheafification preserves finite colimits because it is a left adjoint. -/
noncomputable instance topPresheafToSheafPreservesFiniteColimits (Y : TopCat.{0}) :
    PreservesFiniteColimits (topPresheafToSheaf Y) := by
  change PreservesFiniteColimits
    (presheafToSheaf (Opens.grothendieckTopology Y) (IntModuleCat.{0}))
  infer_instance

/-- Integer-module sheafification is additive. -/
noncomputable instance topPresheafToSheafAdditive (Y : TopCat.{0}) :
    (topPresheafToSheaf Y).Additive := by
  let F := topPresheafToSheaf Y
  letI : F.PreservesZeroMorphisms := inferInstance
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

/-- Integer-module sheafification preserves categorical homology. -/
noncomputable instance topPresheafToSheafPreservesHomology (Y : TopCat.{0}) :
    (topPresheafToSheaf Y).PreservesHomology := by
  let F := topPresheafToSheaf Y
  exact ((Functor.exact_tfae F).out 3 2 rfl rfl).mp ⟨inferInstance, inferInstance⟩

/-- Integer-module sheafification maps exact short complexes to exact short complexes. -/
theorem topPresheafToSheaf_map_exact (Y : TopCat.{0})
    (S : ShortComplex (TopCat.Presheaf (IntModuleCat.{0}) Y)) (hS : S.Exact) :
    (S.map (topPresheafToSheaf Y)).Exact := by
  let F := topPresheafToSheaf Y
  exact (((Functor.exact_tfae F).out 2 1 rfl rfl).mp inferInstance) S hS

/-- Degreewise integer-module sheafification maps quasi-isomorphisms of nonnegative chain
complexes to quasi-isomorphisms. -/
theorem topPresheafToSheaf_map_quasiIso (Y : TopCat.{0})
    {K L : IntModulePresheafChainComplex Y} (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (((topPresheafToSheaf Y).mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ) := by
  exact HomologicalComplex.quasiIso_map_of_preservesHomology φ _

end GaloisForLFunctions.IrregularStokes.ExactSheafification
