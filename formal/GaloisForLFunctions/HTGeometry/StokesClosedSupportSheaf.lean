import GaloisForLFunctions.HTGeometry.StokesEnhancedEpigraphConvolution
import GaloisForLFunctions.HTGeometry.StokesBorderedSpace
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Ordinary sheaves on closed exponential supports

Constant additive sheaves on closed subspaces, pushed to the ambient space.  This is an
underived ordinary-sheaf construction.  It does not construct enhanced ind-sheaves or extension by
zero along a locally closed inclusion.

Mathlib's available `AddCommGrpCat` sheafification instances make this file intentionally
universe-0.
-/

namespace GaloisForLFunctions.IrregularStokes.ClosedSupportSheaf

open CategoryTheory TopologicalSpace TopCat Topology
open GaloisForLFunctions.IrregularStokes.EnhancedEpigraph

/-- Continuous subtype inclusion as a morphism of topological spaces. -/
def subtypeInclusion {X : Type} [TopologicalSpace X] (S : Set X) :
    TopCat.of S ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Inclusion of nested subspaces. -/
def nestedSubtypeInclusion {X : Type} [TopologicalSpace X] {S T : Set X} (hST : S ⊆ T) :
    TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨fun x => ⟨x.1, hST x.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- Subtype inclusion of a closed set is a closed embedding. -/
theorem subtypeInclusion_isClosedEmbedding {X : Type} [TopologicalSpace X] {S : Set X}
    (hS : IsClosed S) : IsClosedEmbedding (subtypeInclusion S).hom := by
  simpa [subtypeInclusion] using hS.isClosedEmbedding_subtypeVal

/-- Nested subtype inclusions compose to the ambient subtype inclusion. -/
theorem nestedSubtypeInclusion_comp {X : Type} [TopologicalSpace X] {S T : Set X}
    (hST : S ⊆ T) :
    nestedSubtypeInclusion hST ≫ subtypeInclusion T = subtypeInclusion S := by
  ext x
  rfl

/-- Constant additive sheaf, obtained by sheafifying the constant presheaf. -/
noncomputable def constantAddCommGrpSheaf (X : TopCat) (A : AddCommGrpCat) :
    TopCat.Sheaf AddCommGrpCat X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A

/-- Direct image of the constant sheaf on a closed subset. -/
noncomputable def constantClosedSupportSheaf {X : Type} [TopologicalSpace X]
    (S : Set X) (_hS : IsClosed S) (A : AddCommGrpCat) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of X) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (subtypeInclusion S)).obj
    (constantAddCommGrpSheaf (TopCat.of S) A)

/-- Direct images of sheaves compose canonically. -/
def pushforwardComp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : TopCat.Sheaf AddCommGrpCat X) :
    (TopCat.Sheaf.pushforward AddCommGrpCat (f ≫ g)).obj F ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat g).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) where
  hom := ⟨(TopCat.Presheaf.Pushforward.comp f g F.1).hom⟩
  inv := ⟨(TopCat.Presheaf.Pushforward.comp f g F.1).inv⟩
  hom_inv_id := by
    refine CategoryTheory.Sheaf.hom_ext ?_
    exact (TopCat.Presheaf.Pushforward.comp f g F.1).hom_inv_id
  inv_hom_id := by
    refine CategoryTheory.Sheaf.hom_ext ?_
    exact (TopCat.Presheaf.Pushforward.comp f g F.1).inv_hom_id

/-- A closed-support sheaf factors canonically through every intermediate closed support. -/
noncomputable def constantClosedSupportSheafFactorization {X : Type} [TopologicalSpace X]
    {S T : Set X} (hS : IsClosed S) (_hT : IsClosed T) (hST : S ⊆ T)
    (A : AddCommGrpCat) :
    constantClosedSupportSheaf S hS A ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat (subtypeInclusion T)).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat (nestedSubtypeInclusion hST)).obj
          (constantAddCommGrpSheaf (TopCat.of S) A)) := by
  unfold constantClosedSupportSheaf
  rw [← nestedSubtypeInclusion_comp hST]
  exact pushforwardComp (nestedSubtypeInclusion hST) (subtypeInclusion T)
    (constantAddCommGrpSheaf (TopCat.of S) A)

/-- Ordinary additive sheaf carried by a continuous phase's closed exponential epigraph. -/
noncomputable def exponentialClosedSupportSheaf {X : Type} [TopologicalSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) (A : AddCommGrpCat) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (X × ℝ)) :=
  constantClosedSupportSheaf (exponentialEpigraph φ) (isClosed_exponentialEpigraph hφ) A

/-- Exponential support inclusion is a closed embedding for a continuous phase. -/
theorem exponentialSubtypeInclusion_isClosedEmbedding {X : Type} [TopologicalSpace X]
    {φ : X → ℝ} (hφ : Continuous φ) :
    IsClosedEmbedding (subtypeInclusion (exponentialEpigraph φ)).hom :=
  subtypeInclusion_isClosedEmbedding (isClosed_exponentialEpigraph hφ)

end GaloisForLFunctions.IrregularStokes.ClosedSupportSheaf
