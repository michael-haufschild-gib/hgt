import GaloisForLFunctions.RHTower.CCMRationalAdelicMoritaRepresentation
import GaloisForLFunctions.RHTower.CyclicBarTraceMorphism
import Mathlib.Analysis.Normed.Algebra.UnitizationL1

/-!
# Trace-class Morita algebra and normalized unitized trace

The fixed-base CCM representation lands in the nonunital algebra of trace-class operators on
`ℓ²(ℚˣ)`.  This file constructs that algebra as an actual `NonUnitalSubalgebra`, proves closure
under every algebra operation, and unitizes it before defining the normalized trace

`(z,T) ↦ z + Tr(T)`.

This separation is essential: the identity operator on `ℓ²(ℚˣ)` is not trace class.  Thus the
unitized trace cannot be defined by pretending that ordinary operator trace applies to the unit.
-/

noncomputable section

open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra
private abbrev MoritaOperator :=
  CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert

theorem ccmRationalZeroOperator_isTraceClass :
    (0 : MoritaOperator).IsTraceClass := by
  have h := ccmRationalAdelicMoritaRepresentation_isTraceClass
    (bInf := (1 : ℝ)) one_ne_zero (1 : CCMRationalFiniteAdeleˣ) (0 : Crossed)
  simpa using h

theorem ccmRationalIsTraceClass_smul
    {T : MoritaOperator} (hT : T.IsTraceClass) (z : ℂ) :
    (z • T).IsTraceClass :=
  (_root_.RHTower.memSchattenClass_one_smul
    (_root_.RHTower.IsTraceClass.memSchattenClass_one hT) z).one_isTraceClass

theorem ccmRationalIsTraceClass_mul
    {S T : MoritaOperator} (hS : S.IsTraceClass) (_hT : T.IsTraceClass) :
    (S * T).IsTraceClass := by
  rw [ContinuousLinearMap.mul_def]
  exact (_root_.RHTower.memSchattenClass_one_comp_right
    (_root_.RHTower.IsTraceClass.memSchattenClass_one hS) T).one_isTraceClass

/-- Nonunital algebra of trace-class operators on the actual rational Morita Hilbert space. -/
def ccmRationalMoritaTraceClassSubalgebra :
    NonUnitalSubalgebra ℂ MoritaOperator where
  carrier := {T | T.IsTraceClass}
  zero_mem' := ccmRationalZeroOperator_isTraceClass
  add_mem' := fun hS hT => ccmRationalIsTraceClass_add hS hT
  mul_mem' := fun hS hT => ccmRationalIsTraceClass_mul hS hT
  smul_mem' := fun z _ hT => ccmRationalIsTraceClass_smul hT z

/-- Actual trace-class Morita ideal, with inherited nonunital complex-algebra structure. -/
abbrev CCMRationalMoritaTraceClassOperator :=
  ccmRationalMoritaTraceClassSubalgebra

noncomputable instance ccmRationalMoritaTraceClassNormedSpace :
    NormedSpace ℂ CCMRationalMoritaTraceClassOperator where
  norm_smul_le z T := by
    change ‖z • (T : MoritaOperator)‖ ≤ ‖z‖ * ‖(T : MoritaOperator)‖
    exact norm_smul_le z (T : MoritaOperator)

/-- Ordinary operator trace restricted to the trace-class Morita ideal. -/
def ccmRationalMoritaOperatorTrace :
    CCMRationalMoritaTraceClassOperator →ₗ[ℂ] ℂ where
  toFun T := opTrace (T : MoritaOperator)
  map_add' S T := by
    exact _root_.RHTower.opTrace_add_of_memSchattenClass_one
      (_root_.RHTower.IsTraceClass.memSchattenClass_one S.property)
      (_root_.RHTower.IsTraceClass.memSchattenClass_one T.property)
  map_smul' z T := by
    exact _root_.RHTower.opTrace_smul z (T : MoritaOperator)

/-- Cyclicity of ordinary trace on the genuine trace-class Morita algebra. -/
theorem ccmRationalMoritaOperatorTrace_isTrace
    (S T : CCMRationalMoritaTraceClassOperator) :
    ccmRationalMoritaOperatorTrace (S * T) =
      ccmRationalMoritaOperatorTrace (T * S) := by
  change opTrace ((S : MoritaOperator) * (T : MoritaOperator)) =
    opTrace ((T : MoritaOperator) * (S : MoritaOperator))
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  exact _root_.RHTower.MemSchattenClass.one_opTrace_comp_comm
    (_root_.RHTower.IsTraceClass.memSchattenClass_one T.property)
    (S : MoritaOperator)

/-- Minimal unitization of the actual trace-class Morita ideal. -/
abbrev CCMRationalMoritaTraceClassUnitization :=
  Unitization ℂ CCMRationalMoritaTraceClassOperator

/-- Minimal unitization with its natural `ℓ¹` norm `|z| + ‖T‖`. -/
abbrev CCMRationalMoritaTraceClassL1Unitization :=
  WithLp 1 CCMRationalMoritaTraceClassUnitization

noncomputable instance ccmRationalMoritaTraceClassL1NormedAddCommGroup :
    NormedAddCommGroup CCMRationalMoritaTraceClassL1Unitization :=
  WithLp.instUnitizationNormedAddCommGroup ℂ CCMRationalMoritaTraceClassOperator

noncomputable instance ccmRationalMoritaTraceClassL1NormedRing :
    NormedRing CCMRationalMoritaTraceClassL1Unitization :=
  WithLp.instUnitizationNormedRing

noncomputable instance ccmRationalMoritaTraceClassL1NormedAlgebra :
    NormedAlgebra ℂ CCMRationalMoritaTraceClassL1Unitization :=
  WithLp.instUnitizationNormedAlgebra

/-- Normalized trace on the unitization: scalar unit plus trace-class operator trace. -/
def ccmRationalMoritaUnitizedTrace :
    CCMRationalMoritaTraceClassUnitization →ₗ[ℂ] ℂ where
  toFun x := x.fst + ccmRationalMoritaOperatorTrace x.snd
  map_add' x y := by
    simp only [Unitization.fst_add, Unitization.snd_add, map_add]
    ring
  map_smul' z x := by
    simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem ccmRationalMoritaUnitizedTrace_one :
    ccmRationalMoritaUnitizedTrace
      (1 : CCMRationalMoritaTraceClassUnitization) = 1 := by
  simp [ccmRationalMoritaUnitizedTrace]

@[simp]
theorem ccmRationalMoritaUnitizedTrace_inr
    (T : CCMRationalMoritaTraceClassOperator) :
    ccmRationalMoritaUnitizedTrace
        (T : CCMRationalMoritaTraceClassUnitization) =
      ccmRationalMoritaOperatorTrace T := by
  simp [ccmRationalMoritaUnitizedTrace]

theorem ccmRationalMoritaUnitizedTrace_isTrace
    (x y : CCMRationalMoritaTraceClassUnitization) :
    ccmRationalMoritaUnitizedTrace (x * y) =
      ccmRationalMoritaUnitizedTrace (y * x) := by
  change (x * y).fst + ccmRationalMoritaOperatorTrace (x * y).snd =
    (y * x).fst + ccmRationalMoritaOperatorTrace (y * x).snd
  rw [Unitization.fst_mul, Unitization.fst_mul,
    Unitization.snd_mul, Unitization.snd_mul]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [ccmRationalMoritaOperatorTrace_isTrace x.snd y.snd]
  ring

/-- Exact fixed-base representation into the trace-class Morita algebra. -/
def ccmRationalAdelicMoritaTraceClassHom
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Crossed →ₙₐ[ℂ] CCMRationalMoritaTraceClassOperator where
  toFun F :=
    ⟨ccmRationalAdelicMoritaRepresentation hbInf b F,
      ccmRationalAdelicMoritaRepresentation_isTraceClass hbInf b F⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' F H := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' z F := by
    apply Subtype.ext
    exact map_smul _ _ _
  map_mul' F H := by
    apply Subtype.ext
    simpa [ContinuousLinearMap.mul_def] using
      ccmRationalAdelicMoritaRepresentation_mul hbInf b F H

/-- Unitized exact CCM representation; the scalar unit is represented algebraically, not as a
trace-class identity operator. -/
def ccmRationalAdelicMoritaUnitizedHom
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Source →ₐ[ℂ] CCMRationalMoritaTraceClassUnitization :=
  Unitization.lift
    ((Unitization.inrNonUnitalAlgHom ℂ CCMRationalMoritaTraceClassOperator).comp
      (ccmRationalAdelicMoritaTraceClassHom hbInf b))

/-- Normed `ℓ¹`-unitized form of the exact fixed-base CCM representation. -/
def ccmRationalAdelicMoritaL1UnitizedHom
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Source →ₐ[ℂ] CCMRationalMoritaTraceClassL1Unitization :=
  (WithLp.unitizationAlgEquiv ℂ).symm.toAlgHom.comp
    (ccmRationalAdelicMoritaUnitizedHom hbInf b)

@[simp]
theorem ccmRationalAdelicMoritaL1UnitizedHom_ofLp
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (x : Source) :
    WithLp.ofLp (ccmRationalAdelicMoritaL1UnitizedHom hbInf b x) =
      ccmRationalAdelicMoritaUnitizedHom hbInf b x :=
  rfl

/-- Fixed-base normalized Morita trace on the exact CCM cyclic source. -/
def ccmRationalAdelicMoritaTrace
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Source →ₗ[ℂ] ℂ :=
  ccmRationalMoritaUnitizedTrace.comp
    (ccmRationalAdelicMoritaUnitizedHom hbInf b).toLinearMap

theorem ccmRationalAdelicMoritaTrace_isTrace
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (x y : Source) :
    ccmRationalAdelicMoritaTrace hbInf b (x * y) =
      ccmRationalAdelicMoritaTrace hbInf b (y * x) := by
  change ccmRationalMoritaUnitizedTrace
      (ccmRationalAdelicMoritaUnitizedHom hbInf b (x * y)) =
    ccmRationalMoritaUnitizedTrace
      (ccmRationalAdelicMoritaUnitizedHom hbInf b (y * x))
  have hxy : ccmRationalAdelicMoritaUnitizedHom hbInf b (x * y) =
      ccmRationalAdelicMoritaUnitizedHom hbInf b x *
        ccmRationalAdelicMoritaUnitizedHom hbInf b y :=
    map_mul (ccmRationalAdelicMoritaUnitizedHom hbInf b) x y
  have hyx : ccmRationalAdelicMoritaUnitizedHom hbInf b (y * x) =
      ccmRationalAdelicMoritaUnitizedHom hbInf b y *
        ccmRationalAdelicMoritaUnitizedHom hbInf b x :=
    map_mul (ccmRationalAdelicMoritaUnitizedHom hbInf b) y x
  rw [hxy, hyx]
  exact ccmRationalMoritaUnitizedTrace_isTrace _ _

/-- All-degree cyclic trace morphism at one genuine adelic Morita base. -/
def ccmRationalAdelicMoritaTraceCyclicHom
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    CyclicModule.Hom
      (cyclicBarCyclicModule (R := ℂ) (A := Source))
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom
    (ccmRationalAdelicMoritaTrace hbInf b)
    (ccmRationalAdelicMoritaTrace_isTrace hbInf b)

end RHTower
end GaloisForLFunctions
