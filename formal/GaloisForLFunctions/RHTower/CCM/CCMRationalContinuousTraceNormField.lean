import GaloisForLFunctions.RHTower.CCM.CCMRationalMoritaTraceNormAlgebra
import GaloisForLFunctions.RHTower.CCM.CCMRationalClassSpaceSection
import GaloisForLFunctions.RHTower.KRealCyclicBar

/-!
# Continuous trace-norm fields on the rational class space

This is the operator-valued ambient algebra in CCM Definition 4.9: continuous maps from the
canonical section `Ẑˣ × ℝ₊ˣ` to the genuine Schatten-`1` minimal unitization.  Continuity is for
the actual trace norm, not the bounded-operator norm.  Fiberwise quaternionic conjugation and
right class-space translation are bundled and proved compatible with normalized trace.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Continuous fields with values in the genuine trace-norm minimal unitization. -/
abbrev CCMRationalContinuousTraceNormField :=
  C(CCMRationalClassSpaceSection, CCMRationalMoritaTraceNormL1Unitization)

/-- Fiberwise quaternionic Real involution on continuous trace-norm fields. -/
def ccmRationalContinuousTraceNormFieldReal
    (F : CCMRationalContinuousTraceNormField) :
    CCMRationalContinuousTraceNormField where
  toFun b := ccmRationalMoritaTraceNormL1RealStructure (F b)
  continuous_toFun :=
    ccmRationalMoritaTraceNormL1RealIsometry.continuous.comp F.continuous

@[simp]
theorem ccmRationalContinuousTraceNormFieldReal_apply
    (F : CCMRationalContinuousTraceNormField)
    (b : CCMRationalClassSpaceSection) :
    ccmRationalContinuousTraceNormFieldReal F b =
      ccmRationalMoritaTraceNormL1RealStructure (F b) :=
  rfl

@[simp]
theorem ccmRationalContinuousTraceNormFieldReal_add
    (F G : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldReal (F + G) =
      ccmRationalContinuousTraceNormFieldReal F +
        ccmRationalContinuousTraceNormFieldReal G := by
  ext b
  exact ccmRationalMoritaTraceNormL1RealStructure_add (F b) (G b)

@[simp]
theorem ccmRationalContinuousTraceNormFieldReal_smul
    (z : ℂ) (F : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldReal (z • F) =
      star z • ccmRationalContinuousTraceNormFieldReal F := by
  ext b
  exact ccmRationalMoritaTraceNormL1RealStructure_smul z (F b)

@[simp]
theorem ccmRationalContinuousTraceNormFieldReal_mul
    (F G : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldReal (F * G) =
      ccmRationalContinuousTraceNormFieldReal F *
        ccmRationalContinuousTraceNormFieldReal G := by
  ext b
  exact ccmRationalMoritaTraceNormL1RealStructure_mul (F b) (G b)

@[simp]
theorem ccmRationalContinuousTraceNormFieldReal_one :
    ccmRationalContinuousTraceNormFieldReal
      (1 : CCMRationalContinuousTraceNormField) = 1 := by
  ext b
  exact ccmRationalMoritaTraceNormL1RealStructure_one

@[simp]
theorem ccmRationalContinuousTraceNormFieldReal_sq
    (F : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldReal
        (ccmRationalContinuousTraceNormFieldReal F) = F := by
  ext b
  exact ccmRationalMoritaTraceNormL1RealStructure_sq (F b)

/-- Target Real structure is genuinely trace-norm isometric at every class-space point. -/
theorem ccmRationalContinuousTraceNormFieldReal_norm
    (F : CCMRationalContinuousTraceNormField)
    (b : CCMRationalClassSpaceSection) :
    ‖ccmRationalContinuousTraceNormFieldReal F b‖ = ‖F b‖ :=
  ccmRationalMoritaTraceNormL1RealStructure_norm (F b)

/-- Conjugate-linear bundle for the field Real structure. -/
def ccmRationalContinuousTraceNormFieldRealₛₗ :
    CCMRationalContinuousTraceNormField →ₗ⋆[ℂ]
      CCMRationalContinuousTraceNormField where
  toFun := ccmRationalContinuousTraceNormFieldReal
  map_add' := ccmRationalContinuousTraceNormFieldReal_add
  map_smul' := ccmRationalContinuousTraceNormFieldReal_smul

/-- Exact even Real algebra structure on the ambient continuous-field algebra. -/
def ccmRationalContinuousTraceNormFieldKRealAlgebra :
    KRealAlgebraStructure CCMRationalContinuousTraceNormField where
  sigma := ccmRationalContinuousTraceNormFieldRealₛₗ
  sq F := by
    change ccmRationalContinuousTraceNormFieldReal
        (ccmRationalContinuousTraceNormFieldReal F) =
      kRealParityAction false F
    rw [ccmRationalContinuousTraceNormFieldReal_sq]
    rfl
  map_one := ccmRationalContinuousTraceNormFieldReal_one
  map_mul := ccmRationalContinuousTraceNormFieldReal_mul

/-- Continuous normalized trace of a continuous trace-norm field. -/
def ccmRationalContinuousTraceNormFieldTrace
    (F : CCMRationalContinuousTraceNormField) :
    C(CCMRationalClassSpaceSection, ℂ) where
  toFun b := ccmRationalMoritaTraceNormL1Trace (F b)
  continuous_toFun :=
    ccmRationalMoritaTraceNormL1Trace.continuous.comp F.continuous

/-- Field trace as a complex-linear map. -/
def ccmRationalContinuousTraceNormFieldTraceLinear :
    CCMRationalContinuousTraceNormField →ₗ[ℂ]
      C(CCMRationalClassSpaceSection, ℂ) where
  toFun := ccmRationalContinuousTraceNormFieldTrace
  map_add' F G := by
    ext b
    exact map_add ccmRationalMoritaTraceNormL1Trace (F b) (G b)
  map_smul' z F := by
    ext b
    exact map_smul ccmRationalMoritaTraceNormL1Trace z (F b)

@[simp]
theorem ccmRationalContinuousTraceNormFieldTrace_apply
    (F : CCMRationalContinuousTraceNormField)
    (b : CCMRationalClassSpaceSection) :
    ccmRationalContinuousTraceNormFieldTrace F b =
      ccmRationalMoritaTraceNormL1Trace (F b) :=
  rfl

/-- Normalized field trace is cyclic pointwise. -/
theorem ccmRationalContinuousTraceNormFieldTrace_isTrace
    (F G : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldTrace (F * G) =
      ccmRationalContinuousTraceNormFieldTrace (G * F) := by
  ext b
  exact ccmRationalMoritaTraceNormL1Trace_isTrace (F b) (G b)

/-- Normalized field trace intertwines target Real structure and complex conjugation. -/
theorem ccmRationalContinuousTraceNormFieldTrace_real
    (F : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldTrace
        (ccmRationalContinuousTraceNormFieldReal F) =
      star (ccmRationalContinuousTraceNormFieldTrace F) := by
  ext b
  exact ccmRationalMoritaTraceNormL1Trace_real (F b)

/-- Right multiplication on the canonical rational class-space section. -/
def ccmRationalClassSpaceRightMul
    (c : CCMRationalClassSpaceSection) :
    C(CCMRationalClassSpaceSection, CCMRationalClassSpaceSection) where
  toFun b := b * c
  continuous_toFun := continuous_id.mul continuous_const

/-- Right regular action on continuous trace-norm fields. -/
def ccmRationalContinuousTraceNormFieldRightAction
    (c : CCMRationalClassSpaceSection)
    (F : CCMRationalContinuousTraceNormField) :
    CCMRationalContinuousTraceNormField :=
  F.comp (ccmRationalClassSpaceRightMul c)

@[simp]
theorem ccmRationalContinuousTraceNormFieldRightAction_apply
    (c : CCMRationalClassSpaceSection)
    (F : CCMRationalContinuousTraceNormField)
    (b : CCMRationalClassSpaceSection) :
    ccmRationalContinuousTraceNormFieldRightAction c F b = F (b * c) :=
  rfl

/-- Right regular action is a unital algebra endomorphism. -/
def ccmRationalContinuousTraceNormFieldRightActionAlgHom
    (c : CCMRationalClassSpaceSection) :
    CCMRationalContinuousTraceNormField →ₐ[ℂ]
      CCMRationalContinuousTraceNormField where
  toFun := ccmRationalContinuousTraceNormFieldRightAction c
  map_one' := by ext b; rfl
  map_mul' F G := by ext b; rfl
  map_zero' := by ext b; rfl
  map_add' F G := by ext b; rfl
  commutes' z := by ext b; rfl

@[simp]
theorem ccmRationalContinuousTraceNormFieldRightAction_one
    (F : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldRightAction 1 F = F := by
  ext b
  simp

theorem ccmRationalContinuousTraceNormFieldRightAction_mul
    (c d : CCMRationalClassSpaceSection)
    (F : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldRightAction c
        (ccmRationalContinuousTraceNormFieldRightAction d F) =
      ccmRationalContinuousTraceNormFieldRightAction (c * d) F := by
  ext b
  simp [mul_assoc]

theorem ccmRationalContinuousTraceNormFieldRightAction_real
    (c : CCMRationalClassSpaceSection)
    (F : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldRightAction c
        (ccmRationalContinuousTraceNormFieldReal F) =
      ccmRationalContinuousTraceNormFieldReal
        (ccmRationalContinuousTraceNormFieldRightAction c F) := by
  ext b
  rfl

theorem ccmRationalContinuousTraceNormFieldTrace_rightAction
    (c : CCMRationalClassSpaceSection)
    (F : CCMRationalContinuousTraceNormField) :
    ccmRationalContinuousTraceNormFieldTrace
        (ccmRationalContinuousTraceNormFieldRightAction c F) =
      (ccmRationalContinuousTraceNormFieldTrace F).comp
        (ccmRationalClassSpaceRightMul c) := by
  ext b
  rfl

end RHTower
end GaloisForLFunctions
