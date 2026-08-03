import GaloisForLFunctions.RHTower.CCMRationalMoritaTraceClassAlgebra
import GaloisForLFunctions.RHTower.CCMRationalHilbertOperatorRealStructure
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# The genuine trace-norm Morita ideal

The trace-class subtype inherited from bounded operators carries the operator norm.  CCM's
analytic target instead uses the Schatten `1` norm.  This file puts the genuine trace norm on a
separate copy of that subtype, proves its normed-ideal algebra structure, forms the minimal
`ℓ¹` unitization, and extends quaternionic Real conjugation isometrically.
-/

noncomputable section

open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev H := CCMRationalMoritaHilbert
private abbrev Op := H →L[ℂ] H
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

/-- A separate copy of the actual trace-class ideal, equipped below with the Schatten `1` norm. -/
@[ext]
structure CCMRationalMoritaTraceNormOperator where
  toTraceClass : CCMRationalMoritaTraceClassOperator

/-- Forgetting the trace norm gives the existing actual trace-class operator subtype. -/
def ccmRationalMoritaTraceNormOperatorEquiv :
    CCMRationalMoritaTraceNormOperator ≃ CCMRationalMoritaTraceClassOperator where
  toFun := CCMRationalMoritaTraceNormOperator.toTraceClass
  invFun := fun T => ⟨T⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance ccmRationalMoritaTraceNormOperatorNonUnitalRing :
    NonUnitalRing CCMRationalMoritaTraceNormOperator :=
  ccmRationalMoritaTraceNormOperatorEquiv.nonUnitalRing

noncomputable instance ccmRationalMoritaTraceNormOperatorModule :
    Module ℂ CCMRationalMoritaTraceNormOperator :=
  Equiv.module ℂ ccmRationalMoritaTraceNormOperatorEquiv

@[simp]
theorem ccmRationalMoritaTraceNormOperator_toTraceClass_zero :
    (0 : CCMRationalMoritaTraceNormOperator).toTraceClass = 0 :=
  rfl

@[simp]
theorem ccmRationalMoritaTraceNormOperator_toTraceClass_add
    (S T : CCMRationalMoritaTraceNormOperator) :
    (S + T).toTraceClass = S.toTraceClass + T.toTraceClass :=
  rfl

@[simp]
theorem ccmRationalMoritaTraceNormOperator_toTraceClass_smul
    (z : ℂ) (T : CCMRationalMoritaTraceNormOperator) :
    (z • T).toTraceClass = z • T.toTraceClass :=
  rfl

@[simp]
theorem ccmRationalMoritaTraceNormOperator_toTraceClass_mul
    (S T : CCMRationalMoritaTraceNormOperator) :
    (S * T).toTraceClass = S.toTraceClass * T.toTraceClass :=
  rfl

theorem ccmRationalMoritaTraceNormOperator_summable
    (T : CCMRationalMoritaTraceNormOperator) :
    Summable (fun n =>
      _root_.RHTower.approxNumber (T.toTraceClass : Op) n) := by
  simpa [_root_.RHTower.MemSchattenClass, Real.rpow_one] using
    _root_.RHTower.IsTraceClass.memSchattenClass_one
      T.toTraceClass.property

theorem ccmRationalMoritaTraceNormOperator_isCompact
    (T : CCMRationalMoritaTraceNormOperator) :
    IsCompactOperator (T.toTraceClass : Op) := by
  obtain ⟨A, B, hA, hB, hT⟩ := T.toTraceClass.property
  rw [hT]
  exact (hB.comp_left A).isCompactOperator

noncomputable instance ccmRationalMoritaTraceNormOperatorNorm :
    Norm CCMRationalMoritaTraceNormOperator where
  norm T := _root_.RHTower.traceNorm H (T.toTraceClass : Op)

private theorem ccmRationalMoritaTraceNormOperatorNormedSpaceCore :
    NormedSpace.Core ℂ CCMRationalMoritaTraceNormOperator where
  norm_nonneg T :=
    _root_.RHTower.traceNorm_nonneg (T.toTraceClass : Op)
  norm_eq_zero_iff T := by
    change _root_.RHTower.traceNorm H (T.toTraceClass : Op) = 0 ↔ T = 0
    rw [_root_.RHTower.traceNorm_eq_zero_iff
      (ccmRationalMoritaTraceNormOperator_summable T)]
    constructor
    · intro h
      apply CCMRationalMoritaTraceNormOperator.ext
      apply Subtype.ext
      exact h
    · rintro rfl
      rfl
  norm_smul z T :=
    _root_.RHTower.traceNorm_smul z (T.toTraceClass : Op)
  norm_triangle S T := by
    change _root_.RHTower.traceNorm H
        ((S.toTraceClass : Op) + (T.toTraceClass : Op)) ≤
      _root_.RHTower.traceNorm H (S.toTraceClass : Op) +
        _root_.RHTower.traceNorm H (T.toTraceClass : Op)
    exact _root_.RHTower.traceNorm_add_le
      (ccmRationalMoritaTraceNormOperator_isCompact S)
      (ccmRationalMoritaTraceNormOperator_isCompact T)
      (ccmRationalMoritaTraceNormOperator_summable S)
      (ccmRationalMoritaTraceNormOperator_summable T)

noncomputable instance ccmRationalMoritaTraceNormOperatorNormedAddCommGroup :
    NormedAddCommGroup CCMRationalMoritaTraceNormOperator :=
  NormedAddCommGroup.ofCore
    ccmRationalMoritaTraceNormOperatorNormedSpaceCore

noncomputable instance ccmRationalMoritaTraceNormOperatorNormedSpace :
    NormedSpace ℂ CCMRationalMoritaTraceNormOperator :=
  NormedSpace.ofCore ccmRationalMoritaTraceNormOperatorNormedSpaceCore

noncomputable instance ccmRationalMoritaTraceNormOperatorNonUnitalNormedRing :
    NonUnitalNormedRing CCMRationalMoritaTraceNormOperator :=
  { (inferInstance : NormedAddCommGroup CCMRationalMoritaTraceNormOperator),
    (inferInstance : NonUnitalRing CCMRationalMoritaTraceNormOperator) with
    norm_mul_le S T := by
      change _root_.RHTower.traceNorm H
          ((S.toTraceClass : Op) ∘L (T.toTraceClass : Op)) ≤
        _root_.RHTower.traceNorm H (S.toTraceClass : Op) *
          _root_.RHTower.traceNorm H (T.toTraceClass : Op)
      refine (_root_.RHTower.traceNorm_comp_right_le
        (ccmRationalMoritaTraceNormOperator_summable S)
        (T.toTraceClass : Op)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (_root_.RHTower.norm_le_traceNorm
          (ccmRationalMoritaTraceNormOperator_summable T))
        (_root_.RHTower.traceNorm_nonneg (S.toTraceClass : Op)) }

noncomputable instance ccmRationalMoritaTraceNormOperatorSMulCommClass :
    SMulCommClass ℂ CCMRationalMoritaTraceNormOperator
      CCMRationalMoritaTraceNormOperator where
  smul_comm z S T := by
    apply ccmRationalMoritaTraceNormOperatorEquiv.injective
    exact smul_comm z S.toTraceClass T.toTraceClass

noncomputable instance ccmRationalMoritaTraceNormOperatorIsScalarTower :
    IsScalarTower ℂ CCMRationalMoritaTraceNormOperator
      CCMRationalMoritaTraceNormOperator where
  smul_assoc z S T := by
    apply ccmRationalMoritaTraceNormOperatorEquiv.injective
    exact smul_assoc z S.toTraceClass T.toTraceClass

/-- The norm on the new ideal is definitionally the genuine Schatten `1` norm. -/
@[simp]
theorem ccmRationalMoritaTraceNormOperator_norm
    (T : CCMRationalMoritaTraceNormOperator) :
    ‖T‖ = _root_.RHTower.traceNorm H (T.toTraceClass : Op) :=
  rfl

/-- Minimal unitization of the genuine trace-norm ideal. -/
abbrev CCMRationalMoritaTraceNormUnitization :=
  Unitization ℂ CCMRationalMoritaTraceNormOperator

/-- Exact `|z| + ‖T‖₁` norm on the minimal unitization. -/
abbrev CCMRationalMoritaTraceNormL1Unitization :=
  WithLp 1 CCMRationalMoritaTraceNormUnitization

noncomputable instance ccmRationalMoritaTraceNormL1NormedAddCommGroup :
    NormedAddCommGroup CCMRationalMoritaTraceNormL1Unitization :=
  WithLp.instUnitizationNormedAddCommGroup ℂ
    CCMRationalMoritaTraceNormOperator

noncomputable instance ccmRationalMoritaTraceNormL1NormedRing :
    NormedRing CCMRationalMoritaTraceNormL1Unitization :=
  WithLp.instUnitizationNormedRing

noncomputable instance ccmRationalMoritaTraceNormL1NormedAlgebra :
    NormedAlgebra ℂ CCMRationalMoritaTraceNormL1Unitization :=
  WithLp.instUnitizationNormedAlgebra

@[simp]
theorem ccmRationalMoritaTraceNormL1_norm
    (x : CCMRationalMoritaTraceNormL1Unitization) :
    ‖x‖ = ‖(WithLp.ofLp x).fst‖ +
      _root_.RHTower.traceNorm H
        ((WithLp.ofLp x).snd.toTraceClass : Op) := by
  rw [WithLp.unitization_norm_def]
  rfl

/-! ## Exact fixed-base representation -/

/-- Fixed-base representation into the genuine trace-norm ideal. -/
def ccmRationalAdelicMoritaTraceNormHom
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Crossed →ₙₐ[ℂ] CCMRationalMoritaTraceNormOperator where
  toFun F := ⟨ccmRationalAdelicMoritaTraceClassHom hbInf b F⟩
  map_zero' := by ext; simp
  map_add' F G := by ext; simp
  map_smul' z F := by ext; simp
  map_mul' F G := by ext; simp

/-- Unitized representation into the exact trace-norm unitization. -/
def ccmRationalAdelicMoritaTraceNormUnitizedHom
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Source →ₐ[ℂ] CCMRationalMoritaTraceNormUnitization :=
  Unitization.lift
    ((Unitization.inrNonUnitalAlgHom ℂ
      CCMRationalMoritaTraceNormOperator).comp
      (ccmRationalAdelicMoritaTraceNormHom hbInf b))

/-- Normed form of the exact unitized representation. -/
def ccmRationalAdelicMoritaTraceNormL1UnitizedHom
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Source →ₐ[ℂ] CCMRationalMoritaTraceNormL1Unitization :=
  (WithLp.unitizationAlgEquiv ℂ).symm.toAlgHom.comp
    (ccmRationalAdelicMoritaTraceNormUnitizedHom hbInf b)

@[simp]
theorem ccmRationalAdelicMoritaTraceNormL1UnitizedHom_ofLp
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (x : Source) :
    WithLp.ofLp
        (ccmRationalAdelicMoritaTraceNormL1UnitizedHom hbInf b x) =
      ccmRationalAdelicMoritaTraceNormUnitizedHom hbInf b x :=
  rfl

/-! ## Quaternionic Real conjugation in trace norm -/

/-- Quaternionic Real conjugation restricted to the trace-norm ideal. -/
def ccmRationalMoritaTraceNormRealStructure
    (T : CCMRationalMoritaTraceNormOperator) :
    CCMRationalMoritaTraceNormOperator :=
  ⟨⟨ccmRationalMoritaHilbertOperatorRealStructure
      (T.toTraceClass : Op),
    ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass
      T.toTraceClass.property⟩⟩

@[simp]
theorem ccmRationalMoritaTraceNormRealStructure_toOperator
    (T : CCMRationalMoritaTraceNormOperator) :
    ((ccmRationalMoritaTraceNormRealStructure T).toTraceClass : Op) =
      ccmRationalMoritaHilbertOperatorRealStructure
        (T.toTraceClass : Op) :=
  rfl

theorem ccmRationalMoritaTraceNormRealStructure_add
    (S T : CCMRationalMoritaTraceNormOperator) :
    ccmRationalMoritaTraceNormRealStructure (S + T) =
      ccmRationalMoritaTraceNormRealStructure S +
        ccmRationalMoritaTraceNormRealStructure T := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  exact ccmRationalMoritaHilbertOperatorRealStructure_add _ _

theorem ccmRationalMoritaTraceNormRealStructure_smul
    (z : ℂ) (T : CCMRationalMoritaTraceNormOperator) :
    ccmRationalMoritaTraceNormRealStructure (z • T) =
      star z • ccmRationalMoritaTraceNormRealStructure T := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  exact ccmRationalMoritaHilbertOperatorRealStructure_smul z _

theorem ccmRationalMoritaTraceNormRealStructure_mul
    (S T : CCMRationalMoritaTraceNormOperator) :
    ccmRationalMoritaTraceNormRealStructure (S * T) =
      ccmRationalMoritaTraceNormRealStructure S *
        ccmRationalMoritaTraceNormRealStructure T := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  change ccmRationalMoritaHilbertOperatorRealStructure
      ((S.toTraceClass : Op) ∘L (T.toTraceClass : Op)) =
    ccmRationalMoritaHilbertOperatorRealStructure (S.toTraceClass : Op) ∘L
      ccmRationalMoritaHilbertOperatorRealStructure (T.toTraceClass : Op)
  exact ccmRationalMoritaHilbertOperatorRealStructure_comp _ _

theorem ccmRationalMoritaTraceNormRealStructure_sq
    (T : CCMRationalMoritaTraceNormOperator) :
    ccmRationalMoritaTraceNormRealStructure
        (ccmRationalMoritaTraceNormRealStructure T) = T := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  exact ccmRationalMoritaHilbertOperatorRealStructure_sq _

@[simp]
theorem ccmRationalMoritaTraceNormRealStructure_zero :
    ccmRationalMoritaTraceNormRealStructure
      (0 : CCMRationalMoritaTraceNormOperator) = 0 := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  change -ccmRationalMoritaHilbertReflection
      ((0 : Op) (ccmRationalMoritaHilbertReflection f)) = 0
  have h := ccmRationalMoritaHilbertReflection_smul
    (0 : ℂ) (0 : CCMRationalMoritaHilbert)
  rw [zero_apply, show ccmRationalMoritaHilbertReflection 0 = 0 by
    simpa only [zero_smul, star_zero] using h]
  exact neg_zero

@[simp]
theorem ccmRationalMoritaTraceNormRealStructure_norm
    (T : CCMRationalMoritaTraceNormOperator) :
    ‖ccmRationalMoritaTraceNormRealStructure T‖ = ‖T‖ :=
  ccmRationalMoritaHilbertOperatorRealStructure_traceNorm _

/-- Trace-norm-isometric conjugate-linear involution on the exact ideal. -/
def ccmRationalMoritaTraceNormRealIsometry :
    CCMRationalMoritaTraceNormOperator ≃ₗᵢ⋆[ℂ]
      CCMRationalMoritaTraceNormOperator where
  toFun := ccmRationalMoritaTraceNormRealStructure
  invFun := ccmRationalMoritaTraceNormRealStructure
  left_inv := ccmRationalMoritaTraceNormRealStructure_sq
  right_inv := ccmRationalMoritaTraceNormRealStructure_sq
  map_add' := ccmRationalMoritaTraceNormRealStructure_add
  map_smul' := ccmRationalMoritaTraceNormRealStructure_smul
  norm_map' := ccmRationalMoritaTraceNormRealStructure_norm

/-- Real involution on the algebraic minimal unitization. -/
def ccmRationalMoritaTraceNormUnitizedRealStructure
    (x : CCMRationalMoritaTraceNormUnitization) :
    CCMRationalMoritaTraceNormUnitization :=
  Unitization.equiv.symm
    (star x.fst, ccmRationalMoritaTraceNormRealStructure x.snd)

@[simp]
theorem ccmRationalMoritaTraceNormUnitizedRealStructure_fst
    (x : CCMRationalMoritaTraceNormUnitization) :
    (ccmRationalMoritaTraceNormUnitizedRealStructure x).fst = star x.fst :=
  rfl

@[simp]
theorem ccmRationalMoritaTraceNormUnitizedRealStructure_snd
    (x : CCMRationalMoritaTraceNormUnitization) :
    (ccmRationalMoritaTraceNormUnitizedRealStructure x).snd =
      ccmRationalMoritaTraceNormRealStructure x.snd :=
  rfl

theorem ccmRationalMoritaTraceNormUnitizedRealStructure_add
    (x y : CCMRationalMoritaTraceNormUnitization) :
    ccmRationalMoritaTraceNormUnitizedRealStructure (x + y) =
      ccmRationalMoritaTraceNormUnitizedRealStructure x +
        ccmRationalMoritaTraceNormUnitizedRealStructure y := by
  apply Unitization.ext <;>
    simp [ccmRationalMoritaTraceNormRealStructure_add]

theorem ccmRationalMoritaTraceNormUnitizedRealStructure_smul
    (z : ℂ) (x : CCMRationalMoritaTraceNormUnitization) :
    ccmRationalMoritaTraceNormUnitizedRealStructure (z • x) =
      star z • ccmRationalMoritaTraceNormUnitizedRealStructure x := by
  apply Unitization.ext <;>
    simp [ccmRationalMoritaTraceNormRealStructure_smul]

theorem ccmRationalMoritaTraceNormUnitizedRealStructure_mul
    (x y : CCMRationalMoritaTraceNormUnitization) :
    ccmRationalMoritaTraceNormUnitizedRealStructure (x * y) =
      ccmRationalMoritaTraceNormUnitizedRealStructure x *
        ccmRationalMoritaTraceNormUnitizedRealStructure y := by
  apply Unitization.ext
  · simp
  · simp only [Unitization.snd_mul,
      ccmRationalMoritaTraceNormUnitizedRealStructure_fst,
      ccmRationalMoritaTraceNormUnitizedRealStructure_snd,
      ccmRationalMoritaTraceNormRealStructure_add,
      ccmRationalMoritaTraceNormRealStructure_smul,
      ccmRationalMoritaTraceNormRealStructure_mul]

theorem ccmRationalMoritaTraceNormUnitizedRealStructure_one :
    ccmRationalMoritaTraceNormUnitizedRealStructure
      (1 : CCMRationalMoritaTraceNormUnitization) = 1 := by
  apply Unitization.ext <;> simp

theorem ccmRationalMoritaTraceNormUnitizedRealStructure_sq
    (x : CCMRationalMoritaTraceNormUnitization) :
    ccmRationalMoritaTraceNormUnitizedRealStructure
        (ccmRationalMoritaTraceNormUnitizedRealStructure x) = x := by
  apply Unitization.ext
  · simp
  · simp [ccmRationalMoritaTraceNormRealStructure_sq]

/-- Real involution on the normed `ℓ¹` unitization. -/
def ccmRationalMoritaTraceNormL1RealStructure
    (x : CCMRationalMoritaTraceNormL1Unitization) :
    CCMRationalMoritaTraceNormL1Unitization :=
  WithLp.toLp 1
    (ccmRationalMoritaTraceNormUnitizedRealStructure (WithLp.ofLp x))

@[simp]
theorem ccmRationalMoritaTraceNormL1RealStructure_ofLp
    (x : CCMRationalMoritaTraceNormL1Unitization) :
    WithLp.ofLp (ccmRationalMoritaTraceNormL1RealStructure x) =
      ccmRationalMoritaTraceNormUnitizedRealStructure (WithLp.ofLp x) :=
  rfl

theorem ccmRationalMoritaTraceNormL1RealStructure_add
    (x y : CCMRationalMoritaTraceNormL1Unitization) :
    ccmRationalMoritaTraceNormL1RealStructure (x + y) =
      ccmRationalMoritaTraceNormL1RealStructure x +
        ccmRationalMoritaTraceNormL1RealStructure y := by
  apply WithLp.ofLp_injective
  simp [ccmRationalMoritaTraceNormUnitizedRealStructure_add]

theorem ccmRationalMoritaTraceNormL1RealStructure_smul
    (z : ℂ) (x : CCMRationalMoritaTraceNormL1Unitization) :
    ccmRationalMoritaTraceNormL1RealStructure (z • x) =
      star z • ccmRationalMoritaTraceNormL1RealStructure x := by
  apply WithLp.ofLp_injective
  simp [ccmRationalMoritaTraceNormUnitizedRealStructure_smul]

theorem ccmRationalMoritaTraceNormL1RealStructure_mul
    (x y : CCMRationalMoritaTraceNormL1Unitization) :
    ccmRationalMoritaTraceNormL1RealStructure (x * y) =
      ccmRationalMoritaTraceNormL1RealStructure x *
        ccmRationalMoritaTraceNormL1RealStructure y := by
  apply WithLp.ofLp_injective
  simp [ccmRationalMoritaTraceNormUnitizedRealStructure_mul]

theorem ccmRationalMoritaTraceNormL1RealStructure_one :
    ccmRationalMoritaTraceNormL1RealStructure
      (1 : CCMRationalMoritaTraceNormL1Unitization) = 1 := by
  apply WithLp.ofLp_injective
  change ccmRationalMoritaTraceNormUnitizedRealStructure 1 = 1
  exact ccmRationalMoritaTraceNormUnitizedRealStructure_one

theorem ccmRationalMoritaTraceNormL1RealStructure_sq
    (x : CCMRationalMoritaTraceNormL1Unitization) :
    ccmRationalMoritaTraceNormL1RealStructure
        (ccmRationalMoritaTraceNormL1RealStructure x) = x := by
  apply WithLp.ofLp_injective
  simp [ccmRationalMoritaTraceNormUnitizedRealStructure_sq]

@[simp]
theorem ccmRationalMoritaTraceNormL1RealStructure_norm
    (x : CCMRationalMoritaTraceNormL1Unitization) :
    ‖ccmRationalMoritaTraceNormL1RealStructure x‖ = ‖x‖ := by
  simp only [ccmRationalMoritaTraceNormL1_norm,
    ccmRationalMoritaTraceNormL1RealStructure_ofLp,
    ccmRationalMoritaTraceNormUnitizedRealStructure_fst,
    ccmRationalMoritaTraceNormUnitizedRealStructure_snd,
    norm_star]
  congr 1
  exact ccmRationalMoritaHilbertOperatorRealStructure_traceNorm _

/-- Isometric conjugate-linear algebra involution on the exact trace-norm unitization. -/
def ccmRationalMoritaTraceNormL1RealIsometry :
    CCMRationalMoritaTraceNormL1Unitization ≃ₗᵢ⋆[ℂ]
      CCMRationalMoritaTraceNormL1Unitization where
  toFun := ccmRationalMoritaTraceNormL1RealStructure
  invFun := ccmRationalMoritaTraceNormL1RealStructure
  left_inv := ccmRationalMoritaTraceNormL1RealStructure_sq
  right_inv := ccmRationalMoritaTraceNormL1RealStructure_sq
  map_add' := ccmRationalMoritaTraceNormL1RealStructure_add
  map_smul' := ccmRationalMoritaTraceNormL1RealStructure_smul
  norm_map' := ccmRationalMoritaTraceNormL1RealStructure_norm

/-! ## Continuous normalized trace -/

/-- Ordinary operator trace as a linear functional on the trace-norm copy. -/
def ccmRationalMoritaTraceNormOperatorTraceLinear :
    CCMRationalMoritaTraceNormOperator →ₗ[ℂ] ℂ where
  toFun T := opTrace (T.toTraceClass : Op)
  map_add' S T := by
    exact _root_.RHTower.opTrace_add_of_memSchattenClass_one
      (_root_.RHTower.IsTraceClass.memSchattenClass_one
        S.toTraceClass.property)
      (_root_.RHTower.IsTraceClass.memSchattenClass_one
        T.toTraceClass.property)
  map_smul' z T :=
    _root_.RHTower.opTrace_smul z (T.toTraceClass : Op)

/-- Ordinary trace, continuous for the genuine trace norm with operator norm at most one. -/
def ccmRationalMoritaTraceNormOperatorTrace :
    CCMRationalMoritaTraceNormOperator →L[ℂ] ℂ :=
  ccmRationalMoritaTraceNormOperatorTraceLinear.mkContinuous 1 fun T => by
    change ‖opTrace (T.toTraceClass : Op)‖ ≤
      1 * _root_.RHTower.traceNorm H (T.toTraceClass : Op)
    simpa only [one_mul] using _root_.RHTower.norm_opTrace_le_traceNorm
      (_root_.RHTower.IsTraceClass.memSchattenClass_one
        T.toTraceClass.property)

@[simp]
theorem ccmRationalMoritaTraceNormOperatorTrace_apply
    (T : CCMRationalMoritaTraceNormOperator) :
    ccmRationalMoritaTraceNormOperatorTrace T =
      opTrace (T.toTraceClass : Op) :=
  rfl

theorem ccmRationalMoritaTraceNormOperatorTrace_real
    (T : CCMRationalMoritaTraceNormOperator) :
    ccmRationalMoritaTraceNormOperatorTrace
        (ccmRationalMoritaTraceNormRealStructure T) =
      star (ccmRationalMoritaTraceNormOperatorTrace T) :=
  ccmRationalMoritaHilbertOperatorRealStructure_opTrace
    T.toTraceClass.property

end RHTower
end GaloisForLFunctions
