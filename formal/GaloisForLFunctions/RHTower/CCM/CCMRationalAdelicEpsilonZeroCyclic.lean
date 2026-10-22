import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonZero
import GaloisForLFunctions.RHTower.CyclicBarTraceMorphism
import GaloisForLFunctions.RHTower.CyclicModuleDoubleKernel

/-!
# The first CCM endpoint as a genuine cyclic-module morphism

This file applies the universal trace-to-cyclic-morphism theorem to the actual minimal unitization
of the rational adelic crossed product.  Thus `ε₀ⁿ` exists in every cyclic degree and is not a
degree-zero proxy.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Genuine tensor cyclic bar of the actual rational CCM source algebra. -/
abbrev CCMRationalAdelicSourceCyclicModule : CyclicModule ℂ :=
  cyclicBarCyclicModule
    (R := ℂ) (A := CCMRationalAdelicCyclicSourceAlgebra)

/-- First CCM endpoint cyclic morphism `ε₀ⁿ`. -/
def ccmRationalAdelicEpsilonZeroCyclicHom :
    CyclicModule.Hom CCMRationalAdelicSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom ccmRationalAdelicEpsilonZero
    ccmRationalAdelicEpsilonZero_isTrace

@[simp]
theorem ccmRationalAdelicEpsilonZeroCyclicHom_app (n : ℕ) :
    ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app (.op (.mk n)) =
      ModuleCat.ofHom
        (cyclicBarTraceAugmentation ccmRationalAdelicEpsilonZero n) :=
  rfl

/-! ## Correct nonunital cyclic module

For a nonunital algebra `A`, `A^♮` is the kernel of the unitization augmentation
`(A⁺)^♮ → ℂ^♮`.  It is not the full cyclic bar of `A⁺`.  We realize this kernel using the
generic cyclic-kernel infrastructure (as the intersection of the augmentation kernel with itself).
-/

private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

/-- Scalar-part augmentation of the minimal unitization. -/
def ccmRationalAdelicUnitizationAugmentation : Source →ₗ[ℂ] ℂ :=
  (Unitization.fstHom ℂ Crossed).toLinearMap

theorem ccmRationalAdelicUnitizationAugmentation_isTrace
    (x y : Source) :
    ccmRationalAdelicUnitizationAugmentation (x * y) =
      ccmRationalAdelicUnitizationAugmentation (y * x) := by
  change (x * y).fst = (y * x).fst
  rw [Unitization.fst_mul, Unitization.fst_mul, mul_comm]

/-- Cyclic augmentation whose kernel is the nonunital cyclic module. -/
def ccmRationalAdelicUnitizationAugmentationCyclicHom :
    CyclicModule.Hom CCMRationalAdelicSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom ccmRationalAdelicUnitizationAugmentation
    ccmRationalAdelicUnitizationAugmentation_isTrace

@[simp]
theorem ccmRationalAdelicUnitizationAugmentationCyclicHom_app (n : ℕ) :
    ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
        (.op (.mk n)) =
      ModuleCat.ofHom
        (cyclicBarTraceAugmentation
          ccmRationalAdelicUnitizationAugmentation n) :=
  rfl

/-- Exact cyclic module of the nonunital rational adelic crossed product. -/
abbrev CCMRationalAdelicNonunitalSourceCyclicModule : CyclicModule ℂ :=
  ccmRationalAdelicUnitizationAugmentationCyclicHom.doubleKernel
    ccmRationalAdelicUnitizationAugmentationCyclicHom

/-- Canonical inclusion of the nonunital cyclic module into the unitized cyclic bar. -/
def ccmRationalAdelicNonunitalSourceCyclicInclusion :
    CyclicModule.Hom CCMRationalAdelicNonunitalSourceCyclicModule
      CCMRationalAdelicSourceCyclicModule :=
  ccmRationalAdelicUnitizationAugmentationCyclicHom.doubleKernelInclusion
    ccmRationalAdelicUnitizationAugmentationCyclicHom

/-- Membership is exactly vanishing of the unitization augmentation. -/
theorem ccmRationalAdelicNonunitalSourceCyclicModule_mem_iff
    (n : ℕ)
    (x : CCMRationalAdelicSourceCyclicModule.simplicial.obj
      (.op (.mk n))) :
    x ∈ ccmRationalAdelicUnitizationAugmentationCyclicHom.doubleKernelSubmodule
        ccmRationalAdelicUnitizationAugmentationCyclicHom (.op (.mk n)) ↔
      ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
        (.op (.mk n)) x = 0 := by
  rw [CyclicModule.Hom.mem_doubleKernelSubmodule_iff]
  exact and_self_iff

/-- In every degree the unitization augmentation is the scalar part of the ordered total product. -/
theorem ccmRationalAdelicUnitizationAugmentationCyclic_eq_totalProduct
    (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    ccmRationalAdelicUnitizationAugmentationCyclicHom.simplicial.app
        (.op (.mk n)) x =
      (cyclicBarTotalProduct n x).fst :=
  rfl

end RHTower
end GaloisForLFunctions
