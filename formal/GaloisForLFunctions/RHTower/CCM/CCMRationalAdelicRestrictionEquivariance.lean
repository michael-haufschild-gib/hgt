import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicClassSpaceSourceAction
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicSourceContinuousTraceNormField

/-!
# Equivariance of exact adelic restriction

The coefficient pullback constructed on the full adelic source realizes right
translation of the continuous Schatten-`1` field over the literal rational
idele-class section.  This is equality of the actual Morita representations,
not merely equality of diagonal traces.
-/

noncomputable section

open ContinuousLinearMap
open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra
private abbrev Section := CCMRationalClassSpaceSection
private abbrev H := CCMRationalMoritaHilbert
private abbrev Op := H →L[ℂ] H

local instance cCMRationalAdelicRestrictionEquivarianceLocalInst1 : DecidableEq Scale := Classical.decEq _

/-- Orbit evaluation after source pullback is evaluation at the translated
class-space base. -/
theorem ccmRationalAdelicBruhatTensorOrbit_classSpaceRightAction
    (c : Section) (t : Core) (bInf : ℝ)
    (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    ccmRationalAdelicBruhatTensorOrbit
        (ccmRationalAdelicBruhatClassSpaceRightAction c t) bInf b q =
      ccmRationalAdelicBruhatTensorOrbit t
        (bInf * (c.2.val : ℝ)) (b * c.1.val) q := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [ccmRationalAdelicBruhatClassSpaceRightAction_tmul,
        ccmRationalAdelicBruhatTensorOrbit_tmul,
        ccmRationalAdelicBruhatPureTensorOrbit,
        ccmRationalClassSpaceArchimedeanRightAction_apply,
        ccmRationalClassSpaceFiniteRightAction_apply]
      congr 2
      · ring
      · rw [Units.val_mul]
        ring
  | add x y hx hy =>
      simp only [map_add, ccmRationalAdelicBruhatTensorOrbit_add, hx, hy]

theorem ccmRationalAdelicBruhatTensorOrbitCoefficient_classSpaceRightAction
    (c : Section) (t : Core) (bInf : ℝ)
    (b : CCMRationalFiniteAdeleˣ) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorOrbitCoefficient
        (ccmRationalAdelicBruhatClassSpaceRightAction c t) bInf b q =
      ccmRationalAdelicBruhatTensorOrbitCoefficient t
        (bInf * (c.2.val : ℝ)) (b * c.1.val) q :=
  ccmRationalAdelicBruhatTensorOrbit_classSpaceRightAction c t bInf b q

/-- Exact covariance of one weighted-shift monomial. -/
theorem ccmRationalAdelicMoritaMonomial_classSpaceRightAction
    (c : Section) (t : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale)
    (hbc : bInf * (c.2.val : ℝ) ≠ 0) :
    ccmRationalAdelicMoritaMonomial
        (ccmRationalAdelicBruhatClassSpaceRightAction c t) hbInf b k =
      ccmRationalAdelicMoritaMonomial t hbc (b * c.1.val) k := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext q
  simp only [ccmRationalAdelicMoritaMonomial,
    ccmRationalAdelicBruhatTensorWeightedShift,
    ccmRationalMoritaWeightedShift_apply]
  rw [ccmRationalAdelicBruhatTensorOrbitCoefficient_classSpaceRightAction]

/-- Exact covariance of the full finite-support crossed-product Morita
representation. -/
theorem ccmRationalAdelicMoritaRepresentation_classSpaceRightAction
    (c : Section) (F : Crossed) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (hbc : bInf * (c.2.val : ℝ) ≠ 0) :
    ccmRationalAdelicMoritaRepresentation hbInf b
        (ccmRationalAdelicCrossedClassSpaceRightAction c F) =
      ccmRationalAdelicMoritaRepresentation hbc (b * c.1.val) F := by
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k t F hkt ht hF =>
      rw [ccmRationalAdelicCrossedClassSpaceRightAction_add,
        ccmRationalAdelicCrossedClassSpaceRightAction_single,
        ccmRationalAdelicMoritaRepresentation_add,
        ccmRationalAdelicMoritaRepresentation_single,
        ccmRationalAdelicMoritaRepresentation_add,
        ccmRationalAdelicMoritaRepresentation_single,
        ccmRationalAdelicMoritaMonomial_classSpaceRightAction c t hbInf b k hbc,
        hF]

theorem ccmRationalAdelicMoritaTraceNormHom_classSpaceRightAction
    (c : Section) (F : Crossed) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (hbc : bInf * (c.2.val : ℝ) ≠ 0) :
    ccmRationalAdelicMoritaTraceNormHom hbInf b
        (ccmRationalAdelicCrossedClassSpaceRightAction c F) =
      ccmRationalAdelicMoritaTraceNormHom hbc (b * c.1.val) F := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  exact ccmRationalAdelicMoritaRepresentation_classSpaceRightAction
    c F hbInf b hbc

/-- Fixed-base covariance survives both exact unitizations. -/
theorem ccmRationalAdelicMoritaTraceNormL1UnitizedHom_classSpaceRightAction
    (c : Section) (x : Source) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (hbc : bInf * (c.2.val : ℝ) ≠ 0) :
    ccmRationalAdelicMoritaTraceNormL1UnitizedHom hbInf b
        (ccmRationalAdelicSourceClassSpaceRightActionHom c x) =
      ccmRationalAdelicMoritaTraceNormL1UnitizedHom hbc (b * c.1.val) x := by
  apply (WithLp.unitizationAlgEquiv ℂ).injective
  change ccmRationalAdelicMoritaTraceNormUnitizedHom hbInf b
      (ccmRationalAdelicSourceClassSpaceRightActionHom c x) =
    ccmRationalAdelicMoritaTraceNormUnitizedHom hbc (b * c.1.val) x
  simp only [ccmRationalAdelicMoritaTraceNormUnitizedHom,
    Unitization.lift_apply]
  change algebraMap ℂ CCMRationalMoritaTraceNormUnitization
      (ccmRationalAdelicSourceClassSpaceRightActionHom c x).fst +
        (ccmRationalAdelicMoritaTraceNormHom hbInf b
          (ccmRationalAdelicSourceClassSpaceRightActionHom c x).snd :
            CCMRationalMoritaTraceNormUnitization) =
    algebraMap ℂ CCMRationalMoritaTraceNormUnitization x.fst +
      (ccmRationalAdelicMoritaTraceNormHom hbc (b * c.1.val) x.snd :
        CCMRationalMoritaTraceNormUnitization)
  rw [ccmRationalAdelicSourceClassSpaceRightActionHom_fst,
    ccmRationalAdelicSourceClassSpaceRightActionHom_snd,
    ccmRationalAdelicMoritaTraceNormHom_classSpaceRightAction
      c x.snd hbInf b hbc]

/-- Full continuous-field restriction intertwines source pullback and literal
right translation on the rational class-space section. -/
theorem ccmRationalAdelicSourceContinuousTraceNormFieldHom_classSpaceRightAction
    (c : Section) (x : Source) :
    ccmRationalAdelicSourceContinuousTraceNormFieldHom
        (ccmRationalAdelicSourceClassSpaceRightActionHom c x) =
      ccmRationalContinuousTraceNormFieldRightAction c
        (ccmRationalAdelicSourceContinuousTraceNormFieldHom x) := by
  apply ContinuousMap.ext
  intro b
  rw [ccmRationalContinuousTraceNormFieldRightAction_apply,
    ccmRationalAdelicSourceContinuousTraceNormFieldHom_apply,
    ccmRationalAdelicSourceContinuousTraceNormFieldHom_apply]
  let hb : (((b.2.val : NNReal) : ℝ)) ≠ 0 := by
    exact ne_of_gt (by
      exact_mod_cast (pos_iff_ne_zero.mpr b.2.ne_zero : 0 < b.2.val))
  let hbc : (((b.2.val : NNReal) : ℝ) * (c.2.val : ℝ)) ≠ 0 :=
    mul_ne_zero hb (by
      exact ne_of_gt (by
        exact_mod_cast (pos_iff_ne_zero.mpr c.2.ne_zero : 0 < c.2.val)))
  exact ccmRationalAdelicMoritaTraceNormL1UnitizedHom_classSpaceRightAction
    c x hb b.1.val hbc

end GaloisForLFunctions.RHTower
