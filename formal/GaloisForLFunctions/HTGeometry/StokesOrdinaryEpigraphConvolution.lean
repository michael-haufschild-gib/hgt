import GaloisForLFunctions.HTGeometry.StokesClosedSupportSheaf
import GaloisForLFunctions.HTGeometry.StokesProperEpigraphAddition
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Ordinary sheaf convolution on exponential epigraphs

An underived convolution bifunctor for sheaves of integer modules on closed exponential supports.
Inputs pull back to the paired epigraph, tensor as presheaves, sheafify, and push forward along
proper fiberwise addition.

This is not derived or enhanced convolution and supplies no irregular Riemann--Hilbert
correspondence.
-/

namespace GaloisForLFunctions.IrregularStokes.OrdinaryConvolution

open CategoryTheory
open EnhancedEpigraph ProperEpigraphAddition
open scoped MonoidalCategory

abbrev IntModuleCat := ModuleCat ℤ

local instance presheafMonoidal (X : TopCat) :
    MonoidalCategory (TopCat.Presheaf IntModuleCat X) :=
  CategoryTheory.Monoidal.functorCategoryMonoidal

variable {X : Type} [TopologicalSpace X]

/-- Constant sheaf of integer modules, obtained by sheafification. -/
noncomputable def constantIntModuleSheaf (Y : TopCat) (A : IntModuleCat) :
    TopCat.Sheaf IntModuleCat Y :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology Y) IntModuleCat).obj A

/-- Tensor product of integer-module sheaves: pointwise presheaf tensor, then sheafification. -/
noncomputable def sheafTensorFunctor (Y : TopCat) :
    TopCat.Sheaf IntModuleCat Y × TopCat.Sheaf IntModuleCat Y ⥤
      TopCat.Sheaf IntModuleCat Y :=
  (TopCat.Sheaf.forget IntModuleCat Y).prod (TopCat.Sheaf.forget IntModuleCat Y) ⋙
    MonoidalCategory.tensor (TopCat.Presheaf IntModuleCat Y) ⋙
      CategoryTheory.presheafToSheaf (Opens.grothendieckTopology Y) IntModuleCat

/-- Projection from the paired epigraph to the first exponential epigraph. -/
def epigraphPairFst (φ ψ : X → ℝ) :
    TopCat.of (exponentialEpigraphPair φ ψ) ⟶ TopCat.of (exponentialEpigraph φ) :=
  TopCat.ofHom
    ⟨fun p => ⟨(p.1.1, p.1.2.1), p.2.1⟩, by
      exact Continuous.subtype_mk
        (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.fst)
        (fun p => p.2.1)⟩

/-- Projection from the paired epigraph to the second exponential epigraph. -/
def epigraphPairSnd (φ ψ : X → ℝ) :
    TopCat.of (exponentialEpigraphPair φ ψ) ⟶ TopCat.of (exponentialEpigraph ψ) :=
  TopCat.ofHom
    ⟨fun p => ⟨(p.1.1, p.1.2.2), p.2.2⟩, by
      exact Continuous.subtype_mk
        (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.snd)
        (fun p => p.2.2)⟩

/-- External tensor on the fiber product of two exponential epigraphs. -/
noncomputable def epigraphExternalTensorFunctor (φ ψ : X → ℝ) :
    TopCat.Sheaf IntModuleCat (TopCat.of (exponentialEpigraph φ)) ×
        TopCat.Sheaf IntModuleCat (TopCat.of (exponentialEpigraph ψ)) ⥤
      TopCat.Sheaf IntModuleCat (TopCat.of (exponentialEpigraphPair φ ψ)) :=
  (TopCat.Sheaf.pullback IntModuleCat (epigraphPairFst φ ψ)).prod
      (TopCat.Sheaf.pullback IntModuleCat (epigraphPairSnd φ ψ)) ⋙
    sheafTensorFunctor (TopCat.of (exponentialEpigraphPair φ ψ))

/-- Continuous epigraph-addition morphism, with continuity obtained from properness. -/
def epigraphFiberwiseAdditionHom (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    TopCat.of (exponentialEpigraphPair φ ψ) ⟶
      TopCat.of (exponentialEpigraph (fun x => φ x + ψ x)) :=
  TopCat.ofHom
    ⟨epigraphFiberwiseAddition φ ψ,
      (epigraphFiberwiseAddition_isProperMap φ ψ hφ hψ).continuous⟩

/-- The topological morphism used by epigraph convolution is proper. -/
theorem epigraphFiberwiseAdditionHom_isProperMap (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    IsProperMap (epigraphFiberwiseAdditionHom φ ψ hφ hψ) := by
  simpa [epigraphFiberwiseAdditionHom] using
    epigraphFiberwiseAddition_isProperMap φ ψ hφ hψ

/-- Ordinary direct image, exposed only with a properness certificate. This does not separately
define a proper-support direct image for nonproper maps. -/
noncomputable def properPushforward {Y Z : TopCat} (f : Y ⟶ Z)
    (_hf : IsProperMap f) :
    TopCat.Sheaf IntModuleCat Y ⥤ TopCat.Sheaf IntModuleCat Z :=
  TopCat.Sheaf.pushforward IntModuleCat f

/-- Underived ordinary convolution on closed exponential supports. -/
noncomputable def ordinaryEpigraphConvolutionFunctor (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    TopCat.Sheaf IntModuleCat (TopCat.of (exponentialEpigraph φ)) ×
        TopCat.Sheaf IntModuleCat (TopCat.of (exponentialEpigraph ψ)) ⥤
      TopCat.Sheaf IntModuleCat
        (TopCat.of (exponentialEpigraph (fun x => φ x + ψ x))) :=
  epigraphExternalTensorFunctor φ ψ ⋙
    properPushforward (epigraphFiberwiseAdditionHom φ ψ hφ hψ)
      (epigraphFiberwiseAdditionHom_isProperMap φ ψ hφ hψ)

/-- Constant integral sheaf on one exponential epigraph. -/
noncomputable def integralExponentialSheaf (φ : X → ℝ) :
    TopCat.Sheaf IntModuleCat (TopCat.of (exponentialEpigraph φ)) :=
  constantIntModuleSheaf (TopCat.of (exponentialEpigraph φ)) (ModuleCat.of ℤ ℤ)

/-- Underived ordinary convolution of two constant integral exponential sheaves. -/
noncomputable def integralOrdinaryEpigraphConvolution (φ ψ : X → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    TopCat.Sheaf IntModuleCat
      (TopCat.of (exponentialEpigraph (fun x => φ x + ψ x))) :=
  (ordinaryEpigraphConvolutionFunctor φ ψ hφ hψ).obj
    (integralExponentialSheaf φ, integralExponentialSheaf ψ)

end GaloisForLFunctions.IrregularStokes.OrdinaryConvolution
