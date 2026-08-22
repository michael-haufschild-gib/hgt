import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimeResidueHT
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature

/-!
# Euler--Wick interaction as Gamma-six opposite-character curvature

The two independent EWQ residue gauges and the two opposite physical Gamma-six characters have
the same nonlinear incidence law after both one-variable marginals are removed.  Evaluating the
anchored two-by-two quotient on the opposite exponential gauges gives exactly the negative product
of their two boundary defects.  This is the positive Gamma-six curvature, expressed in the unique
EWQ interaction direction.

Consequently the resulting interaction class is `curvature / 8` times the normalized Euler--Wick
class.  At a literal prime clock and Xi divisor copy it vanishes exactly on the critical line.  This
is an exact bridge between residue interaction cohomology and physical-character Hodge curvature;
it does not assert a source-natural coupling that annihilates the class.
-/

namespace GaloisForLFunctions.RHTower

open Set
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Binary exponential gauge with the distinguished EWQ anchor fixed at one. -/
def gammaSixOppositeGaugeValue (a : ℝ) (x : Fin 2) : ℂ :=
  if x = 1 then 1 else Complex.ofReal (Real.exp a)

@[simp] theorem gammaSixOppositeGaugeValue_one (a : ℝ) :
    gammaSixOppositeGaugeValue a 1 = 1 := by
  simp [gammaSixOppositeGaugeValue]

@[simp] theorem gammaSixOppositeGaugeValue_zero (a : ℝ) :
    gammaSixOppositeGaugeValue a 0 = Complex.ofReal (Real.exp a) := by
  simp [gammaSixOppositeGaugeValue]

/-- Rank-one opposite-character orbit on the two-gauge square. -/
def gammaSixOppositeGaugeOrbitObservable (a : ℝ) :
    FullValueSubtype (Fin 2 × Fin 2) → ℂ :=
  fun x => gammaSixOppositeGaugeValue a x.1.1 *
    gammaSixOppositeGaugeValue (-a) x.1.2

/-- Remove both one-variable marginals from the opposite-character orbit. -/
def gammaSixOppositeGaugeAnchoredInteraction (a : ℝ) :
    FullValueSubtype (Fin 2 × Fin 2) → ℂ :=
  productAnchoredInteractionPart (Fin 2) (Fin 2)
    (gammaSixOppositeGaugeOrbitObservable a)

/-- Anchoring a rank-one orbit is the product of its two boundary defects. -/
theorem gammaSixOppositeGaugeAnchoredInteraction_eq (a : ℝ)
    (x : FullValueSubtype (Fin 2 × Fin 2)) :
    gammaSixOppositeGaugeAnchoredInteraction a x =
      (gammaSixOppositeGaugeValue a x.1.1 - 1) *
        (gammaSixOppositeGaugeValue (-a) x.1.2 - 1) := by
  simp [gammaSixOppositeGaugeAnchoredInteraction,
    productAnchoredInteractionPart, productRowPart, productColumnPart,
    gammaSixOppositeGaugeOrbitObservable]
  ring

/-- The boundary defect occupies precisely the non-anchor half of the EWQ sign character. -/
theorem gammaSixOppositeGaugeValue_sub_one_eq (a : ℝ) (x : Fin 2) :
    gammaSixOppositeGaugeValue a x - 1 =
      (Complex.ofReal (Real.exp a - 1) / 2) * (1 - finTwoAnchoredSign x) := by
  fin_cases x <;>
    simp [gammaSixOppositeGaugeValue, finTwoAnchoredSign] <;>
    ring

/-- The anchored opposite-character orbit is Gamma-six curvature in the normalized EWQ
interaction direction. -/
theorem gammaSixOppositeGaugeAnchoredInteraction_eq_eulerWick (a : ℝ) :
    gammaSixOppositeGaugeAnchoredInteraction a =
      ((Complex.ofReal
          (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a)) / 8) •
        eulerSquarefreeWickAnchoredInteractionObservable
          eulerSquarefreeWickNormalizedPacket := by
  funext x
  rw [gammaSixOppositeGaugeAnchoredInteraction_eq,
    gammaSixOppositeGaugeValue_sub_one_eq,
    gammaSixOppositeGaugeValue_sub_one_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eulerSquarefreeWickAnchoredInteractionObservable_eq,
    eulerSquarefreeWickNormalizedDefect]
  have hcurv :
      Complex.ofReal
          (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a) =
        -(Complex.ofReal (Real.exp a - 1) *
          Complex.ofReal (Real.exp (-a) - 1)) := by
    rw [_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
      _root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
      _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]
    push_cast
    ring
  rw [hcurv]
  ring

/-- The anchored physical-character observable on the common refinement. -/
def gammaSixOppositeGaugeJointObservable (a : ℝ) :
    ClassInvariantRestricted
      (productFstSetoid (Fin 2) (Fin 2) ⊓ productSndSetoid (Fin 2) (Fin 2)) :=
  ⟨gammaSixOppositeGaugeAnchoredInteraction a, by
    rw [classInvariantRestricted_product_inf_eq_top]
    exact Submodule.mem_top⟩

/-- Cohomology class of the opposite-character physical gauges modulo both marginals. -/
def gammaSixOppositeGaugeInteractionClass (a : ℝ) :
    FiniteQuotientInteractionCohomology
      (productFstSetoid (Fin 2) (Fin 2))
      (productSndSetoid (Fin 2) (Fin 2)) :=
  Submodule.Quotient.mk (gammaSixOppositeGaugeJointObservable a)

/-- Exact cohomological curvature landing in the unique EWQ interaction direction. -/
theorem gammaSixOppositeGaugeInteractionClass_eq_eulerWick (a : ℝ) :
    gammaSixOppositeGaugeInteractionClass a =
      ((Complex.ofReal
          (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a)) / 8) •
        eulerSquarefreeWickInteractionClass eulerSquarefreeWickNormalizedPacket := by
  rw [gammaSixOppositeGaugeInteractionClass, eulerSquarefreeWickInteractionClass]
  change Submodule.Quotient.mk (gammaSixOppositeGaugeJointObservable a) =
    Submodule.Quotient.mk
      (((Complex.ofReal
          (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a)) / 8) •
        eulerSquarefreeWickJointObservable eulerSquarefreeWickNormalizedPacket)
  congr 1
  apply Subtype.ext
  exact gammaSixOppositeGaugeAnchoredInteraction_eq_eulerWick a

/-- The physical-character interaction class has the exact neutral radical. -/
theorem gammaSixOppositeGaugeInteractionClass_eq_zero_iff (a : ℝ) :
    gammaSixOppositeGaugeInteractionClass a = 0 ↔ a = 0 := by
  rw [gammaSixOppositeGaugeInteractionClass_eq_eulerWick, smul_eq_zero]
  have hEWQ : eulerSquarefreeWickInteractionClass
      eulerSquarefreeWickNormalizedPacket ≠ 0 := by
    intro hzero
    have hdefect :=
      (eulerSquarefreeWickInteractionClass_eq_zero_iff _).mp hzero
    rw [eulerSquarefreeWickNormalizedDefect] at hdefect
    norm_num at hdefect
  simp only [hEWQ, or_false]
  rw [div_eq_zero_iff]
  norm_num
  exact _root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a

/-- At a literal prime clock, vanishing of the EWQ-valued physical curvature is exactly critical
line placement of that Xi divisor copy. -/
theorem gammaSixPrimePhysicalGaugeInteractionClass_eq_zero_iff
    (q : _root_.RHTower.XiZeroCopy) (p : Nat.Primes) :
    gammaSixOppositeGaugeInteractionClass
        (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [gammaSixOppositeGaugeInteractionClass_eq_zero_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or]
  exact _root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

end

end GaloisForLFunctions.RHTower
