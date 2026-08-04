import GaloisForLFunctions.RHTower.CCMRationalAdelicSourceContinuousTraceNormField
import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpace
import GaloisForLFunctions.RHTower.CyclicBarModuleValuedTrace
import GaloisForLFunctions.RHTower.CyclicModuleDoubleKernel

/-!
# Literal nonunital CCM strong cyclic target

CCM Definition 4.9 uses the cyclic module of the nonunital algebra
`C(C_Q, L¹(H_x))`.  Its cyclic module is obtained from one global
unitization and then restricted to the augmentation kernel.  It is not the
full cyclic bar of `C(C_Q, (L¹(H_x))⁺)`, which would contain spurious
class-space-dependent scalar fields.

The strong target is the intersection of two exact cyclic kernels:

* global unitization augmentation;
* diagonal normalized trace modulo the literal strong Schwartz space
  `S(C_Q)`.

The second kernel is constructed using a module-valued cyclic trace, because
the strong condition is linear rather than multiplicative.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Ideal := CCMRationalMoritaTraceNormOperator
private abbrev FibreUnit := CCMRationalMoritaTraceNormL1Unitization
private abbrev ScalarFunctions := Section → ℂ
private abbrev StrongScalars := CCMRationalStrongClassSpaceScalarTarget

/-- Actual nonunital algebra of continuous trace-class fields in CCM
Definition 4.9. -/
abbrev CCMRationalContinuousTraceNormIdealField := C(Section, Ideal)

/-- The single global unitization used to construct the cyclic module of the
nonunital field algebra. -/
abbrev CCMRationalContinuousTraceNormIdealFieldUnitization :=
  Unitization ℂ CCMRationalContinuousTraceNormIdealField

private abbrev IdealField := CCMRationalContinuousTraceNormIdealField
private abbrev FieldUnit :=
  CCMRationalContinuousTraceNormIdealFieldUnitization

/-! ## Evaluation and diagonal trace -/

/-- Evaluation of an ideal field followed by the canonical inclusion into the
normed fibre unitization. -/
def ccmRationalContinuousTraceNormIdealFieldEvaluationInr
    (b : Section) : IdealField →ₙₐ[ℂ] FibreUnit where
  toFun F := ccmRationalMoritaTraceNormL1InrHom (F b)
  map_zero' := by simp
  map_add' F G := by simp
  map_smul' z F := by simp
  map_mul' F G :=
    map_mul ccmRationalMoritaTraceNormL1InrHom (F b) (G b)

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldEvaluationInr_apply
    (b : Section) (F : IdealField) :
    ccmRationalContinuousTraceNormIdealFieldEvaluationInr b F =
      ccmRationalMoritaTraceNormL1InrHom (F b) :=
  rfl

/-- Evaluation of the single global unitization in a normed trace-class
fibre. -/
def ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation
    (b : Section) : FieldUnit →ₐ[ℂ] FibreUnit :=
  Unitization.lift
    (ccmRationalContinuousTraceNormIdealFieldEvaluationInr b)

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_inl
    (b : Section) (z : ℂ) :
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b
        (Unitization.inl z) = algebraMap ℂ FibreUnit z := by
  simp [ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation]

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_inr
    (b : Section) (F : IdealField) :
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b
        (F : FieldUnit) =
      ccmRationalMoritaTraceNormL1InrHom (F b) := by
  simp [ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation]

/-- Normalized trace at one class-space point. -/
def ccmRationalNonunitalFieldPointTrace (b : Section) :
    FieldUnit →ₗ[ℂ] ℂ :=
  ccmRationalMoritaTraceNormL1Trace.toLinearMap.comp
    (ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b).toLinearMap

@[simp]
theorem ccmRationalNonunitalFieldPointTrace_apply
    (b : Section) (x : FieldUnit) :
    ccmRationalNonunitalFieldPointTrace b x =
      ccmRationalMoritaTraceNormL1Trace
        (ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b x) :=
  rfl

theorem ccmRationalNonunitalFieldPointTrace_isTrace
    (b : Section) (x y : FieldUnit) :
    ccmRationalNonunitalFieldPointTrace b (x * y) =
      ccmRationalNonunitalFieldPointTrace b (y * x) := by
  let e := ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b
  calc
    ccmRationalNonunitalFieldPointTrace b (x * y) =
        ccmRationalMoritaTraceNormL1Trace (e x * e y) := by
      rw [ccmRationalNonunitalFieldPointTrace_apply,
        show e (x * y) = e x * e y from e.map_mul x y]
    _ = ccmRationalMoritaTraceNormL1Trace (e y * e x) :=
      ccmRationalMoritaTraceNormL1Trace_isTrace _ _
    _ = ccmRationalNonunitalFieldPointTrace b (y * x) := by
      rw [ccmRationalNonunitalFieldPointTrace_apply,
        show e (y * x) = e y * e x from e.map_mul y x]

/-- Pointwise normalized trace of a globally unitized ideal field. -/
def ccmRationalNonunitalFieldTrace :
    FieldUnit →ₗ[ℂ] ScalarFunctions :=
  LinearMap.pi ccmRationalNonunitalFieldPointTrace

@[simp]
theorem ccmRationalNonunitalFieldTrace_apply
    (x : FieldUnit) (b : Section) :
    ccmRationalNonunitalFieldTrace x b =
      ccmRationalNonunitalFieldPointTrace b x :=
  rfl

theorem ccmRationalNonunitalFieldTrace_isTrace (x y : FieldUnit) :
    ccmRationalNonunitalFieldTrace (x * y) =
      ccmRationalNonunitalFieldTrace (y * x) := by
  funext b
  exact ccmRationalNonunitalFieldPointTrace_isTrace b x y

/-- Main-diagonal trace of a cyclic chain in the literal nonunital field
model. -/
def ccmRationalNonunitalStrongDiagonalTrace (n : ℕ) :
    CyclicBarTensor ℂ FieldUnit n →ₗ[ℂ] ScalarFunctions :=
  cyclicBarModuleTraceAugmentation ccmRationalNonunitalFieldTrace n

/-! ## The two cyclic kernels -/

/-- Ambient cyclic bar of the one globally unitized field algebra. -/
abbrev CCMRationalContinuousTraceNormIdealFieldUnitizedCyclicModule :
    CyclicModule ℂ :=
  cyclicBarCyclicModule (R := ℂ) (A := FieldUnit)

/-- Scalar part of the single global unitization. -/
def ccmRationalNonunitalFieldAugmentation : FieldUnit →ₗ[ℂ] ℂ :=
  (Unitization.fstHom ℂ IdealField).toLinearMap

theorem ccmRationalNonunitalFieldAugmentation_isTrace
    (x y : FieldUnit) :
    ccmRationalNonunitalFieldAugmentation (x * y) =
      ccmRationalNonunitalFieldAugmentation (y * x) := by
  change (x * y).fst = (y * x).fst
  rw [Unitization.fst_mul, Unitization.fst_mul, mul_comm]

/-- Cyclic augmentation whose kernel is the cyclic module of the nonunital
ideal-field algebra. -/
def ccmRationalNonunitalFieldAugmentationCyclicHom :
    CyclicModule.Hom
      CCMRationalContinuousTraceNormIdealFieldUnitizedCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom ccmRationalNonunitalFieldAugmentation
    ccmRationalNonunitalFieldAugmentation_isTrace

/-- Diagonal trace followed by quotient modulo the exact strong scalar
subspace. -/
def ccmRationalNonunitalFieldStrongQuotientTrace :
    FieldUnit →ₗ[ℂ] (ScalarFunctions ⧸ StrongScalars) :=
  (Submodule.mkQ StrongScalars).comp ccmRationalNonunitalFieldTrace

theorem ccmRationalNonunitalFieldStrongQuotientTrace_isTrace
    (x y : FieldUnit) :
    ccmRationalNonunitalFieldStrongQuotientTrace (x * y) =
      ccmRationalNonunitalFieldStrongQuotientTrace (y * x) := by
  exact congrArg (Submodule.mkQ StrongScalars)
    (ccmRationalNonunitalFieldTrace_isTrace x y)

/-- Cyclic trace obstruction to the strong diagonal condition. -/
def ccmRationalNonunitalFieldStrongQuotientTraceCyclicHom :
    CyclicModule.Hom
      CCMRationalContinuousTraceNormIdealFieldUnitizedCyclicModule
      (moduleConstantCyclicModule
        (R := ℂ) (M := ScalarFunctions ⧸ StrongScalars)) :=
  cyclicBarModuleTraceCyclicHom
    ccmRationalNonunitalFieldStrongQuotientTrace
    ccmRationalNonunitalFieldStrongQuotientTrace_isTrace

/-- **Literal CCM Definition 4.9 target.** It is simultaneously the cyclic
module of the nonunital trace-class field algebra and the kernel of diagonal
trace modulo `S(C_Q)`. -/
abbrev CCMRationalNonunitalStrongCyclicTarget : CyclicModule ℂ :=
  ccmRationalNonunitalFieldAugmentationCyclicHom.doubleKernel
    ccmRationalNonunitalFieldStrongQuotientTraceCyclicHom

/-- Canonical inclusion into the cyclic bar of the single global
unitization. -/
def ccmRationalNonunitalStrongCyclicInclusion :
    CyclicModule.Hom CCMRationalNonunitalStrongCyclicTarget
      CCMRationalContinuousTraceNormIdealFieldUnitizedCyclicModule :=
  ccmRationalNonunitalFieldAugmentationCyclicHom.doubleKernelInclusion
    ccmRationalNonunitalFieldStrongQuotientTraceCyclicHom

/-- Exact elementwise characterization of Definition 4.9. -/
theorem mem_ccmRationalNonunitalStrongCyclicTarget_iff
    (n : ℕ)
    (x : CCMRationalContinuousTraceNormIdealFieldUnitizedCyclicModule.simplicial.obj
      (.op (.mk n))) :
    x ∈ ccmRationalNonunitalFieldAugmentationCyclicHom.doubleKernelSubmodule
        ccmRationalNonunitalFieldStrongQuotientTraceCyclicHom
        (.op (.mk n)) ↔
      cyclicBarTraceAugmentation
          ccmRationalNonunitalFieldAugmentation n x = 0 ∧
        ccmRationalNonunitalStrongDiagonalTrace n x ∈ StrongScalars := by
  rw [CyclicModule.Hom.mem_doubleKernelSubmodule_iff]
  change
    cyclicBarTraceAugmentation
          ccmRationalNonunitalFieldAugmentation n x = 0 ∧
      Submodule.mkQ StrongScalars
        (ccmRationalNonunitalStrongDiagonalTrace n x) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end GaloisForLFunctions.RHTower
