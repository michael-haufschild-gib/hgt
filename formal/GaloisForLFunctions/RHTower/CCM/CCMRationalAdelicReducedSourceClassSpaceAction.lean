import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicRestrictionEquivariance
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicReducedStrongCyclicHom
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicLefschetz

/-!
# Class-space action on the exact reduced adelic source

The full source algebra action fixes the unitization augmentation and the
zero endpoint.  On the nonunital cyclic kernel it rescales the Haar endpoint
by the nonzero positive radial character.  It therefore restricts twice: first
to the genuine nonunital cyclic module and then to the exact two-endpoint CCM
source.  Exact restriction to strong class-space fields is equivariant.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra
private abbrev Section := CCMRationalClassSpaceSection

/-! ## Endpoint covariance on the full source -/

theorem ccmRationalAdelicEpsilonZero_classSpaceRightAction
    (c : Section) (x : Source) :
    ccmRationalAdelicEpsilonZero
        (ccmRationalAdelicSourceClassSpaceRightActionHom c x) =
      ccmRationalAdelicEpsilonZero x := by
  change (ccmRationalAdelicSourceClassSpaceRightActionHom c x).fst +
      ccmRationalAdelicEpsilonZeroNonunital
        (ccmRationalAdelicSourceClassSpaceRightActionHom c x).snd =
    x.fst + ccmRationalAdelicEpsilonZeroNonunital x.snd
  rw [ccmRationalAdelicSourceClassSpaceRightActionHom_fst,
    ccmRationalAdelicSourceClassSpaceRightActionHom_snd,
    ccmRationalAdelicEpsilonZeroNonunital_classSpaceRightAction]

theorem ccmRationalAdelicEpsilonOne_classSpaceRightAction
    (c : Section) (x : Source) :
    ccmRationalAdelicEpsilonOne
        (ccmRationalAdelicSourceClassSpaceRightActionHom c x) =
      x.fst + ((c.2.val : ℝ)⁻¹) •
        ccmRationalAdelicEpsilonOneNonunital x.snd := by
  change (ccmRationalAdelicSourceClassSpaceRightActionHom c x).fst +
      ccmRationalAdelicEpsilonOneNonunital
        (ccmRationalAdelicSourceClassSpaceRightActionHom c x).snd = _
  rw [ccmRationalAdelicSourceClassSpaceRightActionHom_fst,
    ccmRationalAdelicSourceClassSpaceRightActionHom_snd,
    ccmRationalAdelicEpsilonOneNonunital_classSpaceRightAction]

/-! ## Full cyclic action and product covariance -/

/-- Cyclic-bar action induced by the exact source algebra endomorphism. -/
def ccmRationalAdelicSourceCyclicClassSpaceRightAction (c : Section) :
    CyclicModule.Hom CCMRationalAdelicSourceCyclicModule
      CCMRationalAdelicSourceCyclicModule :=
  cyclicBarAlgHomCyclicHom
    (ccmRationalAdelicSourceClassSpaceRightActionHom c)

@[simp]
theorem ccmRationalAdelicSourceCyclicClassSpaceRightAction_app
    (c : Section) (n : ℕ) :
    (ccmRationalAdelicSourceCyclicClassSpaceRightAction c).simplicial.app
        (.op (.mk n)) =
      ModuleCat.ofHom (cyclicBarAlgHomDegree
        (ccmRationalAdelicSourceClassSpaceRightActionHom c) n) :=
  rfl

theorem cyclicBarTotalProduct_classSpaceRightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x) =
      ccmRationalAdelicSourceClassSpaceRightActionHom c
        (cyclicBarTotalProduct n x) := by
  have h := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      (ccmRationalAdelicSourceClassSpaceRightActionHom c) n) x
  change cyclicBarTotalProduct n
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x) =
    (ccmRationalAdelicSourceClassSpaceRightActionHom c).toLinearMap
      (cyclicBarTotalProduct n x)
  simpa only [LinearMap.comp_apply] using h.symm

theorem ccmRationalAdelicUnitizationAugmentationCyclic_classSpaceRightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
        (.op (.mk n))
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x) =
      ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
        (.op (.mk n)) x := by
  rw [ccmRationalAdelicUnitizationAugmentationCyclic_eq_totalProduct,
    ccmRationalAdelicUnitizationAugmentationCyclic_eq_totalProduct,
    cyclicBarTotalProduct_classSpaceRightAction,
    ccmRationalAdelicSourceClassSpaceRightActionHom_fst]

theorem ccmRationalAdelicEpsilonZeroCyclic_classSpaceRightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app
        (.op (.mk n))
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x) =
      ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app
        (.op (.mk n)) x := by
  rw [ccmRationalAdelicEpsilonZeroCyclic_eq_totalProduct,
    ccmRationalAdelicEpsilonZeroCyclic_eq_totalProduct,
    cyclicBarTotalProduct_classSpaceRightAction,
    ccmRationalAdelicEpsilonZero_classSpaceRightAction]

theorem ccmRationalAdelicEpsilonOneCyclic_classSpaceRightAction_of_nonunital
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n)
    (hx : ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
      (.op (.mk n)) x = 0) :
    ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app
        (.op (.mk n))
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x) =
      ((c.2.val : ℝ)⁻¹) •
        ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app
          (.op (.mk n)) x := by
  have hfst : (cyclicBarTotalProduct n x).fst = 0 := by
    change (cyclicBarTotalProduct n x).fst = 0 at hx
    exact hx
  rw [ccmRationalAdelicEpsilonOneCyclic_eq_totalProduct,
    ccmRationalAdelicEpsilonOneCyclic_eq_totalProduct,
    cyclicBarTotalProduct_classSpaceRightAction,
    ccmRationalAdelicEpsilonOne_classSpaceRightAction]
  change (cyclicBarTotalProduct n x).fst +
      ((c.2.val : ℝ)⁻¹) •
        ccmRationalAdelicEpsilonOneNonunital
          (cyclicBarTotalProduct n x).snd =
    ((c.2.val : ℝ)⁻¹) •
      ((cyclicBarTotalProduct n x).fst +
        ccmRationalAdelicEpsilonOneNonunital
          (cyclicBarTotalProduct n x).snd)
  rw [hfst]
  simp

/-! ## Restriction to the nonunital and reduced cyclic modules -/

/-- The class-space action restricted to the genuine nonunital cyclic module. -/
def ccmRationalAdelicNonunitalSourceCyclicClassSpaceRightAction
    (c : Section) :
    CyclicModule.Hom CCMRationalAdelicNonunitalSourceCyclicModule
      CCMRationalAdelicNonunitalSourceCyclicModule :=
  ccmRationalAdelicUnitizationAugmentationCyclicHom.doubleKernelEnd
    ccmRationalAdelicUnitizationAugmentationCyclicHom
    (ccmRationalAdelicSourceCyclicClassSpaceRightAction c)
    (fun n x hx => by
      change ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
          (.op (.mk n))
          (cyclicBarAlgHomDegree
            (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x) = 0
      rw [ccmRationalAdelicUnitizationAugmentationCyclic_classSpaceRightAction]
      exact hx)
    (fun n x hx => by
      change ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
          (.op (.mk n))
          (cyclicBarAlgHomDegree
            (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x) = 0
      rw [ccmRationalAdelicUnitizationAugmentationCyclic_classSpaceRightAction]
      exact hx)

@[simp]
theorem ccmRationalAdelicNonunitalSourceCyclicClassSpaceRightAction_coe
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicNonunitalSourceCyclicModule.simplicial.degree n) :
    ((ccmRationalAdelicNonunitalSourceCyclicClassSpaceRightAction c).simplicial.app
        (.op (.mk n)) x).1 =
      cyclicBarAlgHomDegree
        (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x.1 :=
  rfl

/-- The zero endpoint kernel is fixed by the nonunital action. -/
theorem ccmRationalAdelicNonunitalEpsilonZero_kernel_preserved
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicNonunitalSourceCyclicModule.simplicial.degree n)
    (hx : ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.simplicial.app
      (.op (.mk n)) x = 0) :
    ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.simplicial.app (.op (.mk n))
        ((ccmRationalAdelicNonunitalSourceCyclicClassSpaceRightAction c).simplicial.app
          (.op (.mk n)) x) = 0 := by
  change ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app (.op (.mk n))
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x.1) = 0
  rw [ccmRationalAdelicEpsilonZeroCyclic_classSpaceRightAction]
  exact hx

/-- The Haar endpoint kernel is preserved after imposing the genuine
nonunital cyclic condition. -/
theorem ccmRationalAdelicNonunitalEpsilonOne_kernel_preserved
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicNonunitalSourceCyclicModule.simplicial.degree n)
    (hx : ccmRationalAdelicNonunitalEpsilonOneCyclicHom.simplicial.app
      (.op (.mk n)) x = 0) :
    ccmRationalAdelicNonunitalEpsilonOneCyclicHom.simplicial.app (.op (.mk n))
        ((ccmRationalAdelicNonunitalSourceCyclicClassSpaceRightAction c).simplicial.app
          (.op (.mk n)) x) = 0 := by
  have hnon :=
    (ccmRationalAdelicNonunitalSourceCyclicModule_mem_iff n x.1).mp x.2
  change ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app (.op (.mk n))
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x.1) = 0
  rw [ccmRationalAdelicEpsilonOneCyclic_classSpaceRightAction_of_nonunital
    c n x.1 hnon]
  change ((c.2.val : ℝ)⁻¹) •
      ccmRationalAdelicNonunitalEpsilonOneCyclicHom.simplicial.app
        (.op (.mk n)) x = 0
  rw [hx, smul_zero]

/-- Exact class-space action on the genuine reduced CCM source. -/
def ccmRationalAdelicReducedSourceCyclicClassSpaceRightAction
    (c : Section) :
    CyclicModule.Hom CCMRationalAdelicReducedSourceCyclicModule
      CCMRationalAdelicReducedSourceCyclicModule :=
  ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.doubleKernelEnd
    ccmRationalAdelicNonunitalEpsilonOneCyclicHom
    (ccmRationalAdelicNonunitalSourceCyclicClassSpaceRightAction c)
    (ccmRationalAdelicNonunitalEpsilonZero_kernel_preserved c)
    (ccmRationalAdelicNonunitalEpsilonOne_kernel_preserved c)

@[simp]
theorem ccmRationalAdelicReducedSourceCyclicClassSpaceRightAction_coe
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.degree n) :
    (((ccmRationalAdelicReducedSourceCyclicClassSpaceRightAction c).simplicial.app
        (.op (.mk n)) x).1).1 =
      cyclicBarAlgHomDegree
        (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x.1.1 :=
  rfl

/-! ## Exact restriction equivariance -/

theorem ccmRationalAdelicReducedStrongCyclicHom_classSpaceRightAction
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.degree n) :
    ccmRationalAdelicReducedStrongCyclicHom.simplicial.app (.op (.mk n))
        ((ccmRationalAdelicReducedSourceCyclicClassSpaceRightAction c).simplicial.app
          (.op (.mk n)) x) =
      (ccmRationalStrongCyclicRightAction c).simplicial.app (.op (.mk n))
        (ccmRationalAdelicReducedStrongCyclicHom.simplicial.app
          (.op (.mk n)) x) := by
  apply Subtype.ext
  change cyclicBarAlgHomDegree
      ccmRationalAdelicSourceContinuousTraceNormFieldHom n
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicSourceClassSpaceRightActionHom c) n x.1.1) =
    cyclicBarAlgHomDegree
      (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n
      (cyclicBarAlgHomDegree
        ccmRationalAdelicSourceContinuousTraceNormFieldHom n x.1.1)
  rw [← cyclicBarAlgHomDegree_comp, ← cyclicBarAlgHomDegree_comp]
  have hAlg :
      ccmRationalAdelicSourceContinuousTraceNormFieldHom.comp
          (ccmRationalAdelicSourceClassSpaceRightActionHom c) =
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c).comp
          ccmRationalAdelicSourceContinuousTraceNormFieldHom := by
    apply AlgHom.ext
    intro y
    exact ccmRationalAdelicSourceContinuousTraceNormFieldHom_classSpaceRightAction c y
  rw [hAlg]

end GaloisForLFunctions.RHTower
