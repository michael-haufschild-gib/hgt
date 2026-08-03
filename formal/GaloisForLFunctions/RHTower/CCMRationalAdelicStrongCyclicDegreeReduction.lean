import GaloisForLFunctions.RHTower.CCMRationalAdelicSourceContinuousTraceNormField
import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonOneCyclic
import GaloisForLFunctions.RHTower.CCMRationalAdelicMoritaTraceFormula
import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicClassSpaceAction

/-!
# Reduction of the full CCM strong cyclic landing to degree zero

The continuous Schatten-`1` representation is an algebra homomorphism.  Consequently, ordered
multiplication of an arbitrary cyclic tensor commutes with that representation.  Taking the
main-diagonal normalized trace therefore loses no information relevant to the strong condition:
in every degree it is exactly the class-space trace of the source tensor's total product.

The two reduced cyclic augmentations are likewise the two endpoint traces of the same total
product.  Thus the analytic landing problem in every cyclic degree is equivalent to one
degree-zero statement: source elements killed by both endpoint traces have strong class-space
trace.  This file proves that reduction, together with the exact pointwise unitized orbit formula.
No landing hypothesis, closure assertion, spectral statement, or numerical computation is hidden.
-/

noncomputable section

open CategoryTheory
open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra
private abbrev Field := CCMRationalContinuousTraceNormField
private abbrev Section := CCMRationalClassSpaceSection

/-- Normalized trace of the exact continuous Schatten-`1` source representation. -/
def ccmRationalAdelicSourceClassSpaceTrace (x : Source) : Section → ℂ :=
  fun b => ccmRationalMoritaTraceNormL1Trace
    (ccmRationalAdelicSourceContinuousTraceNormFieldHom x b)

@[simp]
theorem ccmRationalAdelicSourceClassSpaceTrace_apply
    (x : Source) (b : Section) :
    ccmRationalAdelicSourceClassSpaceTrace x b =
      ccmRationalMoritaTraceNormL1Trace
        (ccmRationalAdelicSourceContinuousTraceNormFieldHom x b) :=
  rfl

/-- Exact unitized degree-zero orbit formula over the literal class-space section. -/
theorem ccmRationalAdelicSourceClassSpaceTrace_eq_orbitSum
    (x : Source) (b : Section) :
    ccmRationalAdelicSourceClassSpaceTrace x b =
      x.fst + ∑' q,
        ccmRationalAdelicBruhatTensorOrbitCoefficient
          (x.snd 1) (((b.2.val : NNReal) : ℝ)) b.1.val q := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      have hbne : (((b.2.val : NNReal) : ℝ)) ≠ 0 := by
        have hbpos : 0 < (((b.2.val : NNReal) : ℝ)) := by
          exact_mod_cast (pos_iff_ne_zero.mpr b.2.ne_zero : 0 < b.2.val)
        exact hbpos.ne'
      simp only [Unitization.fst_add, Unitization.fst_inl,
        Unitization.fst_inr, add_zero, Unitization.snd_add,
        Unitization.snd_inl, Unitization.snd_inr, zero_add]
      rw [ccmRationalAdelicSourceClassSpaceTrace_apply,
        ccmRationalAdelicSourceContinuousTraceNormFieldHom_apply,
        ccmRationalMoritaTraceNormL1Trace_apply,
        ccmRationalAdelicMoritaTraceNormL1UnitizedHom_ofLp]
      rw [map_add]
      have hinl :
          ccmRationalAdelicMoritaTraceNormUnitizedHom hbne b.1.val
              (Unitization.inl z) =
            Unitization.inl z := by
        simp [ccmRationalAdelicMoritaTraceNormUnitizedHom,
          Unitization.algebraMap_eq_inl]
      have hinr :
          ccmRationalAdelicMoritaTraceNormUnitizedHom hbne b.1.val
              (F : Source) =
            (ccmRationalAdelicMoritaTraceNormHom hbne b.1.val F :
              CCMRationalMoritaTraceNormUnitization) := by
        simp [ccmRationalAdelicMoritaTraceNormUnitizedHom]
      rw [hinl, hinr]
      simp only [Unitization.fst_add, Unitization.snd_add,
        Unitization.fst_inl, Unitization.snd_inl,
        Unitization.fst_inr, Unitization.snd_inr, add_zero, zero_add]
      change z + opTrace
          (ccmRationalAdelicMoritaRepresentation hbne b.1.val F) =
        z + ∑' q,
          ccmRationalAdelicBruhatTensorOrbitCoefficient
            (F 1) (((b.2.val : NNReal) : ℝ)) b.1.val q
      rw [ccmRationalAdelicMoritaRepresentation_opTrace_eq_orbitSum]

/-- In every cyclic degree, the target main-diagonal trace is precisely the source class-space
trace of the ordered total product. -/
theorem ccmRationalStrongDiagonalTrace_source_eq_totalProduct
    (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    ccmRationalStrongDiagonalTrace n
        (cyclicBarAlgHomDegree
          ccmRationalAdelicSourceContinuousTraceNormFieldHom n x) =
      ccmRationalAdelicSourceClassSpaceTrace
        (cyclicBarTotalProduct n x) := by
  funext b
  have hproduct := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      ccmRationalAdelicSourceContinuousTraceNormFieldHom n) x
  have hproduct' :
      cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            ccmRationalAdelicSourceContinuousTraceNormFieldHom n x) =
        ccmRationalAdelicSourceContinuousTraceNormFieldHom.toLinearMap
          (cyclicBarTotalProduct n x) := by
    simpa only [LinearMap.comp_apply] using hproduct.symm
  change ccmRationalContinuousTraceNormPointTrace b
      (cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          ccmRationalAdelicSourceContinuousTraceNormFieldHom n x)) = _
  rw [hproduct']
  rfl

/-- The first cyclic augmentation is the first endpoint of the same total product. -/
theorem ccmRationalAdelicEpsilonZeroCyclic_eq_totalProduct
    (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app
        (.op (.mk n)) x =
      ccmRationalAdelicEpsilonZero (cyclicBarTotalProduct n x) :=
  rfl

/-- The second cyclic augmentation is the Haar endpoint of the same total product. -/
theorem ccmRationalAdelicEpsilonOneCyclic_eq_totalProduct
    (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app
        (.op (.mk n)) x =
      ccmRationalAdelicEpsilonOne (cyclicBarTotalProduct n x) :=
  rfl

/-- Exact membership reduction: strong landing of a represented degree-`n` tensor is equivalent
to degree-zero strong landing of its total product. -/
theorem ccmRationalAdelic_source_image_mem_strong_iff_totalProduct
    (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    cyclicBarAlgHomDegree
          ccmRationalAdelicSourceContinuousTraceNormFieldHom n x ∈
        ccmRationalStrongCyclicObjectSubmodule (.mk n) ↔
      ccmRationalAdelicSourceClassSpaceTrace
          (cyclicBarTotalProduct n x) ∈
        CCMRationalStrongClassSpaceScalarTarget := by
  change ccmRationalStrongDiagonalTrace n
      (cyclicBarAlgHomDegree
        ccmRationalAdelicSourceContinuousTraceNormFieldHom n x) ∈
      CCMRationalStrongClassSpaceScalarTarget ↔ _
  rw [ccmRationalStrongDiagonalTrace_source_eq_totalProduct]

/-- Universal all-degree reduction.  Any unconditional proof of the single degree-zero endpoint
landing statement automatically supplies strong landing for the genuine reduced cyclic source in
every degree. -/
theorem ccmRationalAdelic_reduced_source_image_mem_strong_of_degreeZero
    (hlanding : ∀ y : Source,
      y.fst = 0 →
      ccmRationalAdelicEpsilonZero y = 0 →
      ccmRationalAdelicEpsilonOne y = 0 →
      ccmRationalAdelicSourceClassSpaceTrace y ∈
        CCMRationalStrongClassSpaceScalarTarget)
    (n : ℕ)
    (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.obj
      (.op (.mk n))) :
    cyclicBarAlgHomDegree
          ccmRationalAdelicSourceContinuousTraceNormFieldHom n x.1.1 ∈
        ccmRationalStrongCyclicObjectSubmodule (.mk n) := by
  rw [ccmRationalAdelic_source_image_mem_strong_iff_totalProduct]
  apply hlanding
  · have haug := x.1.2.1
    change cyclicBarTraceAugmentation
        ccmRationalAdelicUnitizationAugmentation n x.1.1 = 0 at haug
    exact haug
  · have hx0 := x.2.1
    change cyclicBarTraceAugmentation
        ccmRationalAdelicEpsilonZero n x.1.1 = 0 at hx0
    exact hx0
  · have hx1 := x.2.2
    change cyclicBarTraceAugmentation
        ccmRationalAdelicEpsilonOne n x.1.1 = 0 at hx1
    exact hx1

end RHTower
end GaloisForLFunctions
