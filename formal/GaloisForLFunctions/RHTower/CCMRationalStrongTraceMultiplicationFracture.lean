import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicTarget
import GaloisForLFunctions.RHTower.CCMRationalWeightedShiftLOneIsometry
import GaloisForLFunctions.RHTower.CCMRationalAdelicMoritaMonomial
import GaloisForLFunctions.RHTower.KRealCyclicModule

/-!
# Multiplication fracture of the exact rational CCM strong target

The exact CCM strong condition is cyclic-linear, not multiplicative.  Two explicit off-diagonal
matrix units in the genuine Schatten-`1` Morita fibre have zero normalized trace, whereas their
product is a diagonal matrix unit of trace one.  As constant class-space fields, the first two
therefore satisfy the strong degree-zero condition while their product does not: a nonzero
constant cannot have Meyer's all-exponential-weight logarithmic decay.

This is the precise typing obstruction behind attempts to put an idempotent directly in the
closed cyclic-module cokernel.  The correct recipient for the lifted Real-corona class is
bivariant cyclic theory (an endomorphism/correspondence), not `K₀` of this cyclic cokernel.
-/

noncomputable section

open Complex Filter Function Set Topology
open ContinuousLinearMap

namespace RHTower

/-- A constant has Meyer's all-weight logarithmic decay only when it is zero. -/
theorem deningerMeyerStrongLogDecay_const_iff (z : ℂ) :
    DeningerMeyerStrongLogDecay (fun _ : ℝ => z) ↔ z = 0 := by
  constructor
  · intro hz
    have hO := hz.decayTop 0 1
    rw [iteratedDeriv_zero] at hO
    have hexp :
        Tendsto (fun t : ℝ => Real.exp t ^ (-(1 : ℝ))) atTop (nhds 0) := by
      rw [show (fun t : ℝ => Real.exp t ^ (-(1 : ℝ))) =
          (fun r : ℝ => r⁻¹) ∘ Real.exp by
        funext t
        simp only [Function.comp_apply, Real.rpow_neg_one]]
      exact tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop
    have hzero : Tendsto (fun _ : ℝ => z) atTop (nhds 0) :=
      hO.trans_tendsto hexp
    exact tendsto_nhds_unique tendsto_const_nhds hzero
  · rintro rfl
    change DeningerMeyerStrongLogDecay (0 : ℝ → ℂ)
    exact deningerMeyerStrongLogDecay_zero

end RHTower

namespace GaloisForLFunctions
namespace RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Field := CCMRationalContinuousTraceNormField
private abbrev Ideal := CCMRationalMoritaTraceNormOperator
private abbrev L1Unit := CCMRationalMoritaTraceNormL1Unitization
private abbrev H := CCMRationalMoritaHilbert
private abbrev Op := H →L[ℂ] H

/-- Pointwise normalized trace as a linear map to all scalar class-space functions. -/
def ccmRationalContinuousTraceNormFieldTraceFunctionLinear :
    Field →ₗ[ℂ] (Section → ℂ) :=
  LinearMap.pi fun b => ccmRationalContinuousTraceNormPointTrace b

/-- Exact degree-zero strong condition before the canonical one-tensor identification. -/
def CCMRationalStrongDegreeZeroFieldSubmodule : Submodule ℂ Field :=
  CCMRationalStrongClassSpaceScalarTarget.comap
    ccmRationalContinuousTraceNormFieldTraceFunctionLinear

/-- Canonical one-tensor presentation of a degree-zero cyclic-bar chain. -/
def ccmRationalCyclicBarDegreeZeroTprod (F : Field) :
    CyclicBarTensor ℂ Field 0 :=
  PiTensorProduct.tprod ℂ (fun _ : Fin 1 => F)

/-- The field-level condition is literally the degree-zero component of the exact strong cyclic
target under the canonical one-tensor identification. -/
theorem ccmRationalCyclicBarDegreeZeroTprod_mem_strong_iff (F : Field) :
    ccmRationalCyclicBarDegreeZeroTprod F ∈
        ccmRationalStrongCyclicObjectSubmodule (.mk 0) ↔
      F ∈ CCMRationalStrongDegreeZeroFieldSubmodule := by
  change ccmRationalStrongDiagonalTrace 0
      (ccmRationalCyclicBarDegreeZeroTprod F) ∈
        CCMRationalStrongClassSpaceScalarTarget ↔
    ccmRationalContinuousTraceNormFieldTraceFunctionLinear F ∈
      CCMRationalStrongClassSpaceScalarTarget
  have htrace :
      ccmRationalStrongDiagonalTrace 0
          (ccmRationalCyclicBarDegreeZeroTprod F) =
        ccmRationalContinuousTraceNormFieldTraceFunctionLinear F := by
    funext b
    simp [ccmRationalStrongDiagonalTrace_apply,
      ccmRationalCyclicBarDegreeZeroTprod,
      cyclicBarTotalProduct, cyclicBarDegreeZeroProduct_tprod,
      ccmRationalContinuousTraceNormFieldTraceFunctionLinear]
  rw [htrace]

/-- One-coordinate `ℓ¹(ℚˣ)` coefficient. -/
def ccmRationalMoritaLOneDelta (q₀ : CCMRationalUnit) :
    CCMRationalMoritaLOneCoefficient :=
  lp.single 1 q₀ (1 : ℂ)

@[simp]
theorem ccmRationalMoritaLOneDelta_apply
    (q₀ q : CCMRationalUnit) :
    ccmRationalMoritaLOneDelta q₀ q = if q₀ = q then 1 else 0 := by
  rw [ccmRationalMoritaLOneDelta, lp.single_apply]
  by_cases h : q₀ = q
  · subst q
    simp
  · simp [h, Ne.symm h]

/-- First off-diagonal matrix unit, implemented as the `-1` weighted shift with coefficient
supported at `1`. -/
def ccmRationalMoritaMatrixUnitOneNeg : Ideal :=
  ccmRationalMoritaLOneWeightedShift (-1) (ccmRationalMoritaLOneDelta 1)

/-- Reverse off-diagonal matrix unit, supported at `-1`. -/
def ccmRationalMoritaMatrixUnitNegOne : Ideal :=
  ccmRationalMoritaLOneWeightedShift (-1) (ccmRationalMoritaLOneDelta (-1))

private theorem ccmRationalUnit_negOne_ne_one :
    (-1 : CCMRationalUnit) ≠ 1 := by
  norm_num

/-- Exact trace formula for the genuine `ℓ¹` weighted-shift embedding. -/
theorem ccmRationalMoritaLOneWeightedShift_opTrace
    (k : CCMRationalUnit) (a : CCMRationalMoritaLOneCoefficient) :
    opTrace
        ((ccmRationalMoritaLOneWeightedShift k a).toTraceClass : Op) =
      if k = 1 then ∑' q, a q else 0 := by
  exact ccmRationalMoritaWeightedShift_opTrace
    (fun q => a q) k ‖a‖ (norm_nonneg a)
    (fun q => lp.norm_apply_le_norm (by norm_num) a q)
    (ccmRationalMoritaLOneWeightedShiftOperator_isTraceClass k a)

@[simp]
theorem ccmRationalMoritaMatrixUnitOneNeg_trace :
    ccmRationalMoritaTraceNormOperatorTrace
        ccmRationalMoritaMatrixUnitOneNeg = 0 := by
  rw [ccmRationalMoritaTraceNormOperatorTrace_apply]
  exact (ccmRationalMoritaLOneWeightedShift_opTrace
    (-1) (ccmRationalMoritaLOneDelta 1)).trans
      (if_neg ccmRationalUnit_negOne_ne_one)

@[simp]
theorem ccmRationalMoritaMatrixUnitNegOne_trace :
    ccmRationalMoritaTraceNormOperatorTrace
        ccmRationalMoritaMatrixUnitNegOne = 0 := by
  rw [ccmRationalMoritaTraceNormOperatorTrace_apply]
  exact (ccmRationalMoritaLOneWeightedShift_opTrace
    (-1) (ccmRationalMoritaLOneDelta (-1))).trans
      (if_neg ccmRationalUnit_negOne_ne_one)

private theorem ccmRationalMoritaMatrixUnitProductCoefficient_tsum :
    ∑' q : CCMRationalUnit,
        ccmRationalMoritaWeightedShiftProductCoefficient
          (fun q => ccmRationalMoritaLOneDelta 1 q)
          (fun q => ccmRationalMoritaLOneDelta (-1) q)
          (-1) q = 1 := by
  rw [tsum_eq_single 1]
  · simp [ccmRationalMoritaWeightedShiftProductCoefficient]
  · intro q hq
    simp [ccmRationalMoritaWeightedShiftProductCoefficient, Ne.symm hq]

/-- Matrix-unit product law: the two trace-zero units multiply to trace one. -/
@[simp]
theorem ccmRationalMoritaMatrixUnit_mul_trace :
    ccmRationalMoritaTraceNormOperatorTrace
        (ccmRationalMoritaMatrixUnitOneNeg *
          ccmRationalMoritaMatrixUnitNegOne) = 1 := by
  rw [ccmRationalMoritaTraceNormOperatorTrace_apply]
  change opTrace
      (ccmRationalMoritaLOneWeightedShiftOperator (-1)
          (ccmRationalMoritaLOneDelta 1) ∘L
        ccmRationalMoritaLOneWeightedShiftOperator (-1)
          (ccmRationalMoritaLOneDelta (-1))) = 1
  rw [ccmRationalMoritaLOneWeightedShiftOperator,
    ccmRationalMoritaLOneWeightedShiftOperator,
    ccmRationalMoritaWeightedShift_comp]
  rw [ccmRationalMoritaWeightedShift_opTrace]
  · rw [if_pos (by norm_num)]
    exact ccmRationalMoritaMatrixUnitProductCoefficient_tsum
  · rw [← ccmRationalMoritaWeightedShift_comp]
    exact (ccmRationalMoritaMatrixUnitOneNeg *
      ccmRationalMoritaMatrixUnitNegOne).toTraceClass.property

/-- Ideal element inserted in the minimal `ℓ¹` unitization. -/
def ccmRationalMoritaTraceNormL1IdealElement (T : Ideal) : L1Unit :=
  WithLp.toLp 1 (T : Unitization ℂ Ideal)

@[simp]
theorem ccmRationalMoritaTraceNormL1IdealElement_trace (T : Ideal) :
    ccmRationalMoritaTraceNormL1Trace
        (ccmRationalMoritaTraceNormL1IdealElement T) =
      ccmRationalMoritaTraceNormOperatorTrace T := by
  simp [ccmRationalMoritaTraceNormL1IdealElement,
    ccmRationalMoritaTraceNormL1Trace_apply]

@[simp]
theorem ccmRationalMoritaTraceNormL1IdealElement_mul (S T : Ideal) :
    ccmRationalMoritaTraceNormL1IdealElement S *
        ccmRationalMoritaTraceNormL1IdealElement T =
      ccmRationalMoritaTraceNormL1IdealElement (S * T) := by
  apply WithLp.ofLp_injective
  simp [ccmRationalMoritaTraceNormL1IdealElement]

/-- Constant class-space field attached to a trace-norm ideal element. -/
def ccmRationalMoritaConstantIdealField (T : Ideal) : Field :=
  ContinuousMap.const Section (ccmRationalMoritaTraceNormL1IdealElement T)

@[simp]
theorem ccmRationalMoritaConstantIdealField_apply
    (T : Ideal) (b : Section) :
    ccmRationalMoritaConstantIdealField T b =
      ccmRationalMoritaTraceNormL1IdealElement T :=
  rfl

@[simp]
theorem ccmRationalMoritaConstantIdealField_mul (S T : Ideal) :
    ccmRationalMoritaConstantIdealField S *
        ccmRationalMoritaConstantIdealField T =
      ccmRationalMoritaConstantIdealField (S * T) := by
  ext b
  simp

/-- Zero scalar field lies in the exact strong scalar target. -/
theorem ccmRationalStrongClassSpaceScalarTarget_zero :
    (0 : Section → ℂ) ∈ CCMRationalStrongClassSpaceScalarTarget := by
  exact Submodule.zero_mem _

/-- A nonzero constant scalar field cannot lie in the exact strong target. -/
theorem ccmRationalStrongClassSpaceScalarTarget_const_not_mem
    {z : ℂ} (hz : z ≠ 0) :
    (fun _ : Section => z) ∉ CCMRationalStrongClassSpaceScalarTarget := by
  intro hmem
  rw [mem_ccmRationalStrongClassSpaceScalarTarget_iff] at hmem
  rcases hmem with ⟨f, hf⟩
  have hradial :
      _root_.RHTower.DeningerMeyerStrongLogDecay (fun _ : ℝ => z) := by
    have hfu := (f 1).property
    change _root_.RHTower.DeningerMeyerStrongLogDecay
      (((f 1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)) at hfu
    have heq :
        (fun _ : ℝ => z) =
          ((f 1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) := by
      funext t
      have ht := congrFun hf (1, ccmRationalPositiveLogUnit t)
      simpa [ccmRationalStrongClassSpaceEval] using ht.symm
    rw [heq]
    exact hfu
  exact hz ((_root_.RHTower.deningerMeyerStrongLogDecay_const_iff z).mp hradial)

/-- Both explicit off-diagonal matrix-unit fields satisfy the exact degree-zero strong
condition. -/
theorem ccmRationalMoritaMatrixUnits_mem_strongDegreeZero :
    ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitOneNeg ∈
        CCMRationalStrongDegreeZeroFieldSubmodule ∧
      ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitNegOne ∈
        CCMRationalStrongDegreeZeroFieldSubmodule := by
  constructor
  · change (fun b => ccmRationalMoritaTraceNormL1Trace
        (ccmRationalMoritaConstantIdealField
          ccmRationalMoritaMatrixUnitOneNeg b)) ∈
      CCMRationalStrongClassSpaceScalarTarget
    have htrace :
        (fun b : Section => ccmRationalMoritaTraceNormL1Trace
          (ccmRationalMoritaConstantIdealField
            ccmRationalMoritaMatrixUnitOneNeg b)) = 0 := by
      funext b
      rw [ccmRationalMoritaConstantIdealField_apply,
        ccmRationalMoritaTraceNormL1IdealElement_trace,
        ccmRationalMoritaMatrixUnitOneNeg_trace]
      rfl
    rw [htrace]
    exact ccmRationalStrongClassSpaceScalarTarget_zero
  · change (fun b => ccmRationalMoritaTraceNormL1Trace
        (ccmRationalMoritaConstantIdealField
          ccmRationalMoritaMatrixUnitNegOne b)) ∈
      CCMRationalStrongClassSpaceScalarTarget
    have htrace :
        (fun b : Section => ccmRationalMoritaTraceNormL1Trace
          (ccmRationalMoritaConstantIdealField
            ccmRationalMoritaMatrixUnitNegOne b)) = 0 := by
      funext b
      rw [ccmRationalMoritaConstantIdealField_apply,
        ccmRationalMoritaTraceNormL1IdealElement_trace,
        ccmRationalMoritaMatrixUnitNegOne_trace]
      rfl
    rw [htrace]
    exact ccmRationalStrongClassSpaceScalarTarget_zero

/-- Their product violates the exact strong condition. -/
theorem ccmRationalMoritaMatrixUnitProduct_not_mem_strongDegreeZero :
    ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitOneNeg *
        ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitNegOne ∉
      CCMRationalStrongDegreeZeroFieldSubmodule := by
  rw [ccmRationalMoritaConstantIdealField_mul]
  change (fun b => ccmRationalMoritaTraceNormL1Trace
      (ccmRationalMoritaConstantIdealField
        (ccmRationalMoritaMatrixUnitOneNeg *
          ccmRationalMoritaMatrixUnitNegOne) b)) ∉
      CCMRationalStrongClassSpaceScalarTarget
  have htrace :
      (fun b : Section => ccmRationalMoritaTraceNormL1Trace
        (ccmRationalMoritaConstantIdealField
          (ccmRationalMoritaMatrixUnitOneNeg *
            ccmRationalMoritaMatrixUnitNegOne) b)) =
        (fun _ : Section => (1 : ℂ)) := by
    funext b
    rw [ccmRationalMoritaConstantIdealField_apply,
      ccmRationalMoritaTraceNormL1IdealElement_trace,
      ccmRationalMoritaMatrixUnit_mul_trace]
  rw [htrace]
  exact ccmRationalStrongClassSpaceScalarTarget_const_not_mem one_ne_zero

/-- Literal degree-zero strong cyclic chains corresponding to the two off-diagonal matrix units. -/
theorem ccmRationalMoritaMatrixUnitTprods_mem_strongCyclicDegreeZero :
    ccmRationalCyclicBarDegreeZeroTprod
        (ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitOneNeg) ∈
          ccmRationalStrongCyclicObjectSubmodule (.mk 0) ∧
      ccmRationalCyclicBarDegreeZeroTprod
        (ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitNegOne) ∈
          ccmRationalStrongCyclicObjectSubmodule (.mk 0) := by
  simpa only [ccmRationalCyclicBarDegreeZeroTprod_mem_strong_iff] using
    ccmRationalMoritaMatrixUnits_mem_strongDegreeZero

/-- The literal degree-zero chain associated with their ambient product leaves the strong cyclic
target. -/
theorem ccmRationalMoritaMatrixUnitProductTprod_not_mem_strongCyclicDegreeZero :
    ccmRationalCyclicBarDegreeZeroTprod
        (ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitOneNeg *
          ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitNegOne) ∉
      ccmRationalStrongCyclicObjectSubmodule (.mk 0) := by
  rw [ccmRationalCyclicBarDegreeZeroTprod_mem_strong_iff]
  exact ccmRationalMoritaMatrixUnitProduct_not_mem_strongDegreeZero

/-- **CCM multiplication-fracture law.**  Exact degree-zero strong chains do not form a
subalgebra of the ambient continuous trace-norm field algebra. -/
theorem ccmRationalStrongDegreeZero_not_mul_closed :
    ¬ ∀ x y : Field,
      x ∈ CCMRationalStrongDegreeZeroFieldSubmodule →
      y ∈ CCMRationalStrongDegreeZeroFieldSubmodule →
      x * y ∈ CCMRationalStrongDegreeZeroFieldSubmodule := by
  intro hmul
  exact ccmRationalMoritaMatrixUnitProduct_not_mem_strongDegreeZero
    (hmul _ _
      ccmRationalMoritaMatrixUnits_mem_strongDegreeZero.1
      ccmRationalMoritaMatrixUnits_mem_strongDegreeZero.2)

/-- Exact degree-zero strong submodule is not two-sided. -/
theorem ccmRationalStrongDegreeZero_not_twoSided :
    ¬ IsTwoSidedSubmodule CCMRationalStrongDegreeZeroFieldSubmodule := by
  intro htwo
  exact ccmRationalMoritaMatrixUnitProduct_not_mem_strongDegreeZero
    (htwo.2 _ _ ccmRationalMoritaMatrixUnits_mem_strongDegreeZero.1)

/-- No multiplication with zero absorption can descend to the linear quotient by the exact
degree-zero strong submodule while preserving products of representatives. -/
theorem ccmRationalStrongDegreeZero_no_descended_quotient_multiplication :
    ¬∃ (_ : Mul (Field ⧸ CCMRationalStrongDegreeZeroFieldSubmodule)),
      (∀ x : Field ⧸ CCMRationalStrongDegreeZeroFieldSubmodule, x * 0 = 0) ∧
      (∀ x : Field ⧸ CCMRationalStrongDegreeZeroFieldSubmodule, 0 * x = 0) ∧
      ∀ a b : Field,
        CCMRationalStrongDegreeZeroFieldSubmodule.mkQ (a * b) =
          CCMRationalStrongDegreeZeroFieldSubmodule.mkQ a *
            CCMRationalStrongDegreeZeroFieldSubmodule.mkQ b :=
  no_descended_quotient_multiplication_of_not_twoSided
    CCMRationalStrongDegreeZeroFieldSubmodule
    ccmRationalStrongDegreeZero_not_twoSided

end RHTower
end GaloisForLFunctions
