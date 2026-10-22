import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicTensorPeriodicTracePacket
import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteBruhatProfiniteLocalConstancy
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicStrongCyclicDegreeReduction

/-!
# Full strong class-space landing of the reduced rational CCM source

The pointwise periodic-packet theorem is upgraded here to the literal strong
class-space target.  Uniform profinite stabilizers make every tensor orbit
profile locally constant in `Ẑˣ`; the two endpoint cancellations put each
radial profile in Meyer's all-derivative/all-exponential-weight target.  The
result is an unconditional degree-zero landing theorem for the actual
unitized CCM source, followed by the all-degree reduced cyclic landing through
the exact total-product reduction.
-/

noncomputable section

open CategoryTheory
open scoped RestrictedProduct algebraMap Classical BigOperators

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

/-- Genuine rational-unit logarithmic trace profile of an algebraic adelic
Bruhat tensor at one profinite coordinate. -/
def ccmRationalAdelicTensorUnitLogTrace
    (x : Core) (b : CCMRationalProfiniteUnit) : ℝ → ℂ :=
  fun t => ∑' q : CCMRationalUnit,
    ccmRationalAdelicBruhatTensorOrbit x (Real.exp t) b.1 (q : ℚ)

@[simp]
theorem ccmRationalAdelicTensorUnitLogTrace_zero
    (b : CCMRationalProfiniteUnit) :
    ccmRationalAdelicTensorUnitLogTrace 0 b = 0 := by
  funext t
  simp [ccmRationalAdelicTensorUnitLogTrace]

theorem ccmRationalAdelicTensorUnitLogTrace_add
    (x y : Core) (b : CCMRationalProfiniteUnit) :
    ccmRationalAdelicTensorUnitLogTrace (x + y) b =
      ccmRationalAdelicTensorUnitLogTrace x b +
        ccmRationalAdelicTensorUnitLogTrace y b := by
  funext t
  have hx := summable_norm_iff.mp
    ((ccmRationalAdelicBruhatTensorOrbit_summable x
      (Real.exp_ne_zero t) b.1).comp_injective Units.val_injective)
  have hy := summable_norm_iff.mp
    ((ccmRationalAdelicBruhatTensorOrbit_summable y
      (Real.exp_ne_zero t) b.1).comp_injective Units.val_injective)
  change (∑' q : CCMRationalUnit,
      ccmRationalAdelicBruhatTensorOrbit
        (x + y) (Real.exp t) b.1 (q : ℚ)) = _
  change (∑' q : CCMRationalUnit,
      ccmRationalAdelicBruhatTensorOrbit
        (x + y) (Real.exp t) b.1 (q : ℚ)) =
    (∑' q : CCMRationalUnit,
      ccmRationalAdelicBruhatTensorOrbit
        x (Real.exp t) b.1 (q : ℚ)) +
    ∑' q : CCMRationalUnit,
      ccmRationalAdelicBruhatTensorOrbit
        y (Real.exp t) b.1 (q : ℚ)
  rw [← hx.tsum_add hy]
  apply tsum_congr
  intro q
  rw [ccmRationalAdelicBruhatTensorOrbit_add]

/-- The whole radial trace profile, not merely each scalar evaluation, is
locally constant in the profinite coordinate. -/
theorem ccmRationalAdelicTensorUnitLogTrace_isLocallyConstant
    (x : Core) :
    IsLocallyConstant (ccmRationalAdelicTensorUnitLogTrace x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [show ccmRationalAdelicTensorUnitLogTrace 0 = 0 by
        funext b
        exact ccmRationalAdelicTensorUnitLogTrace_zero b]
      exact IsLocallyConstant.const 0
  | tmul f phi =>
      let T : (CCMRationalFiniteAdele → ℂ) → (ℝ → ℂ) :=
        fun psi t => ∑' q : CCMRationalUnit,
          f (Real.exp t * ((q : ℚ) : ℝ)) *
            psi (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ))
      have hphi :=
        ccmRationalFiniteBruhatMulRight_apply_isLocallyConstant phi
      have hcomp := hphi.comp T
      change IsLocallyConstant (fun b : CCMRationalProfiniteUnit =>
        fun t : ℝ => ∑' q : CCMRationalUnit,
          ccmRationalAdelicBruhatPureTensorOrbit
            f phi (Real.exp t) b.1 (q : ℚ))
      simpa [ccmRationalAdelicBruhatPureTensorOrbit, T,
        Function.comp_def] using hcomp
  | add x y hx hy =>
      rw [show ccmRationalAdelicTensorUnitLogTrace (x + y) =
          ccmRationalAdelicTensorUnitLogTrace x +
            ccmRationalAdelicTensorUnitLogTrace y by
        funext b
        exact ccmRationalAdelicTensorUnitLogTrace_add x y b]
      exact hx.add hy

/-- Exact strong class-space function supplied by both degree-zero endpoints. -/
def ccmRationalAdelicTensorStrongClassSpace
    (x : Core)
    (hzero : ccmRationalAdelicBruhatZeroEval x = 0)
    (hone : ccmRationalAdelicBruhatIntegral x = 0) :
    CCMRationalStrongClassSpace where
  toFun := fun b =>
    ⟨ccmRationalAdelicTensorUnitLogTrace x b,
      ccmRationalAdelicTensor_unitLogTrace_strongLogDecay_of_endpoints
        x b hzero hone⟩
  isLocallyConstant := by
    apply IsLocallyConstant.desc
      (fun b : CCMRationalProfiniteUnit =>
        (⟨ccmRationalAdelicTensorUnitLogTrace x b,
          ccmRationalAdelicTensor_unitLogTrace_strongLogDecay_of_endpoints
            x b hzero hone⟩ :
          _root_.RHTower.DeningerMeyerStrongLogTarget))
      (fun g : _root_.RHTower.DeningerMeyerStrongLogTarget =>
        (g : ℝ → ℂ))
      (by simpa [Function.comp_def] using
        ccmRationalAdelicTensorUnitLogTrace_isLocallyConstant x)
      Subtype.val_injective

@[simp]
theorem ccmRationalAdelicTensorStrongClassSpace_apply
    (x : Core)
    (hzero : ccmRationalAdelicBruhatZeroEval x = 0)
    (hone : ccmRationalAdelicBruhatIntegral x = 0)
    (b : CCMRationalProfiniteUnit) (t : ℝ) :
    ((((ccmRationalAdelicTensorStrongClassSpace x hzero hone) b :
        _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) =
      ccmRationalAdelicTensorUnitLogTrace x b t :=
  rfl

/-- **Unconditional degree-zero strong landing of the actual CCM source.** -/
theorem ccmRationalAdelic_sourceClassSpaceTrace_mem_strong_of_endpoints
    (y : Source)
    (hscalar : y.fst = 0)
    (hzero : ccmRationalAdelicEpsilonZero y = 0)
    (hone : ccmRationalAdelicEpsilonOne y = 0) :
    ccmRationalAdelicSourceClassSpaceTrace y ∈
      CCMRationalStrongClassSpaceScalarTarget := by
  have hzeroCore :
      ccmRationalAdelicBruhatZeroEval (y.snd 1) = 0 := by
    change y.fst + ccmRationalAdelicBruhatZeroEval (y.snd 1) = 0 at hzero
    simpa [hscalar] using hzero
  have honeCore :
      ccmRationalAdelicBruhatIntegral (y.snd 1) = 0 := by
    change y.fst + ccmRationalAdelicBruhatIntegral (y.snd 1) = 0 at hone
    simpa [hscalar] using hone
  refine ⟨ccmRationalAdelicTensorStrongClassSpace
    (y.snd 1) hzeroCore honeCore, ?_⟩
  funext b
  change ccmRationalAdelicTensorUnitLogTrace (y.snd 1) b.1
      (ccmRationalPositiveUnitLog b.2) =
    ccmRationalAdelicSourceClassSpaceTrace y b
  rw [ccmRationalAdelicSourceClassSpaceTrace_eq_orbitSum]
  rw [ccmRationalAdelicTensorUnitLogTrace, hscalar, zero_add]
  apply tsum_congr
  intro q
  simp only [ccmRationalPositiveUnitLog]
  rw [Real.exp_log (ccmRationalPositiveUnit_coe_pos b.2)]
  rfl

/-- **Full all-degree strong landing.** The genuine reduced CCM cyclic module
lands in the exact strong cyclic object in every degree. -/
theorem ccmRationalAdelic_reduced_source_image_mem_strong
    (n : ℕ)
    (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.obj
      (.op (.mk n))) :
    cyclicBarAlgHomDegree
          ccmRationalAdelicSourceContinuousTraceNormFieldHom n x.1.1 ∈
        ccmRationalStrongCyclicObjectSubmodule (.mk n) :=
  ccmRationalAdelic_reduced_source_image_mem_strong_of_degreeZero
    ccmRationalAdelic_sourceClassSpaceTrace_mem_strong_of_endpoints n x

end RHTower
end GaloisForLFunctions
