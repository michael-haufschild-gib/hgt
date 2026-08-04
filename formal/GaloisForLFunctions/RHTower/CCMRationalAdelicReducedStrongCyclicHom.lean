import GaloisForLFunctions.RHTower.CCMRationalAdelicTensorStrongClassSpaceLanding
import GaloisForLFunctions.RHTower.CyclicBarAlgHomMorphism

/-!
# Exact adelic restriction into the CCM strong cyclic target

The reduced rational adelic source was already proved to land degreewise in the
literal CCM Definition 4.9 strong target.  This file performs the missing
categorical step: the degreewise maps are bundled into one cyclic-module
morphism.  Naturality is inherited from cyclic-bar functoriality after passing
through the strong submodule; no coefficientwise class-space surrogate occurs.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

/-- Ambient continuous-field cyclic restriction of the exact reduced source. -/
def ccmRationalAdelicReducedContinuousTraceNormFieldCyclicHom :
    CyclicModule.Hom CCMRationalAdelicReducedSourceCyclicModule
      CCMRationalContinuousTraceNormFieldCyclicModule :=
  CyclicModule.Hom.comp ccmRationalAdelicReducedSourceCyclicInclusion
    (cyclicBarAlgHomCyclicHom
      ccmRationalAdelicSourceContinuousTraceNormFieldHom)

/-- Degreewise restriction into the exact CCM strong submodule. -/
def ccmRationalAdelicReducedStrongCyclicDegree (n : ℕ) :
    CCMRationalAdelicReducedSourceCyclicModule.simplicial.degree n →ₗ[ℂ]
      CCMRationalStrongCyclicTarget.simplicial.degree n where
  toFun x :=
    ⟨cyclicBarAlgHomDegree
        ccmRationalAdelicSourceContinuousTraceNormFieldHom n x.1.1,
      ccmRationalAdelic_reduced_source_image_mem_strong n x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add
      (cyclicBarAlgHomDegree
        ccmRationalAdelicSourceContinuousTraceNormFieldHom n) x.1.1 y.1.1
  map_smul' z x := by
    apply Subtype.ext
    exact map_smul
      (cyclicBarAlgHomDegree
        ccmRationalAdelicSourceContinuousTraceNormFieldHom n) z x.1.1

@[simp]
theorem ccmRationalAdelicReducedStrongCyclicDegree_coe
    (n : ℕ)
    (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicReducedStrongCyclicDegree n x).1 =
      cyclicBarAlgHomDegree
        ccmRationalAdelicSourceContinuousTraceNormFieldHom n x.1.1 :=
  rfl

/-- Degree component over an arbitrary presented simplex. -/
def ccmRationalAdelicReducedStrongCyclicComponent :
    ∀ j : SimplexCategoryGenRelᵒᵖ,
      CCMRationalAdelicReducedSourceCyclicModule.simplicial.obj j ⟶
        CCMRationalStrongCyclicTarget.simplicial.obj j
  | .op (.mk n) =>
      ModuleCat.ofHom (ccmRationalAdelicReducedStrongCyclicDegree n)

@[simp]
theorem ccmRationalAdelicReducedStrongCyclicComponent_mk (n : ℕ) :
    ccmRationalAdelicReducedStrongCyclicComponent (.op (.mk n)) =
      ModuleCat.ofHom (ccmRationalAdelicReducedStrongCyclicDegree n) :=
  rfl

/-- Simplicial restriction into the exact strong target. -/
def ccmRationalAdelicReducedStrongCyclicSimplicialHom :
    CCMRationalAdelicReducedSourceCyclicModule.simplicial ⟶
      CCMRationalStrongCyclicTarget.simplicial where
  app := ccmRationalAdelicReducedStrongCyclicComponent
  naturality {j k} g := by
    rcases j with ⟨⟨j⟩⟩
    rcases k with ⟨⟨k⟩⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h :=
      ccmRationalAdelicReducedContinuousTraceNormFieldCyclicHom.simplicial.naturality g
    change
      ccmRationalAdelicReducedContinuousTraceNormFieldCyclicHom.simplicial.app
          (.op (.mk k))
          (CCMRationalAdelicReducedSourceCyclicModule.simplicial.map g x) =
        CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map g
          (ccmRationalAdelicReducedContinuousTraceNormFieldCyclicHom.simplicial.app
            (.op (.mk j)) x)
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

/-- **Exact full CCM restriction.** The reduced rational adelic cyclic source
maps to the literal continuous-field/strong-diagonal CCM target. -/
def ccmRationalAdelicReducedStrongCyclicHom :
    CyclicModule.Hom CCMRationalAdelicReducedSourceCyclicModule
      CCMRationalStrongCyclicTarget where
  simplicial := ccmRationalAdelicReducedStrongCyclicSimplicialHom
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h :=
      ccmRationalAdelicReducedContinuousTraceNormFieldCyclicHom.cyclic_naturality n
    change
      ccmRationalAdelicReducedContinuousTraceNormFieldCyclicHom.simplicial.app
          (.op (.mk n))
          (CCMRationalAdelicReducedSourceCyclicModule.cyclic n x) =
        CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n
          (ccmRationalAdelicReducedContinuousTraceNormFieldCyclicHom.simplicial.app
            (.op (.mk n)) x)
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

@[simp]
theorem ccmRationalAdelicReducedStrongCyclicHom_app_coe
    (n : ℕ)
    (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicReducedStrongCyclicHom.simplicial.app
        (.op (.mk n)) x).1 =
      cyclicBarAlgHomDegree
        ccmRationalAdelicSourceContinuousTraceNormFieldHom n x.1.1 :=
  rfl

end GaloisForLFunctions.RHTower
