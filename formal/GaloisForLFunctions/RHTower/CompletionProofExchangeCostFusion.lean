import GaloisForLFunctions.HTGeometry.ThreeSlotExchangeabilityInformation
import GaloisForLFunctions.HTGeometry.ConstitutiveExchangeableFormationSelection
import GaloisForLFunctions.RHTower.RouteRCompletionQuantumCostSeparation

/-!
# Proof-exchange, Gamma-cost, and completion-occupation fusion

The reflected logistic laws turn one horizontal grade into a three-slot proof-exchange defect.
This module proves that the Gamma-six paired completion cost is exactly the odds transform of that
defect.  The external completion curvature retains only the defect's zero/nonzero occupation.

This is an unconditional reconstruction law, not a source theorem forcing proof exchange to
vanish.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Three-slot proof-erasure defect of the reflected logistic completion laws. -/
def sourceHorizontalProofExchangeDefect (a : ℝ) : ℝ :=
  threeSlotExchangeDefect (logisticPhase a : ℝ) (logisticPhase (-a) : ℝ)

/-- Gamma completion cost and proof-exchange defect obey one exact conservation identity. -/
theorem sourceHorizontalGammaSixCurvature_mul_proofExchangeComplement
    (a : ℝ) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a *
        (1 - 2 * sourceHorizontalProofExchangeDefect a) =
      8 * sourceHorizontalProofExchangeDefect a := by
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
  simp only [sourceHorizontalProofExchangeDefect, threeSlotExchangeDefect_eq,
    coe_logisticPhase, Real.cosh_eq, Real.exp_neg]
  have hx : 0 < Real.exp a := Real.exp_pos a
  have hxp : Real.exp a ≠ 0 := ne_of_gt hx
  have hsum : 1 + Real.exp a ≠ 0 := by positivity
  field_simp [hxp, hsum]
  ring

/-- The exchange complement is the strictly positive logistic visibility square. -/
theorem one_sub_two_mul_sourceHorizontalProofExchangeDefect_eq (a : ℝ) :
    1 - 2 * sourceHorizontalProofExchangeDefect a =
      4 * Real.exp a / (1 + Real.exp a) ^ 2 := by
  simp only [sourceHorizontalProofExchangeDefect, threeSlotExchangeDefect_eq,
    coe_logisticPhase, Real.exp_neg]
  have hx : 0 < Real.exp a := Real.exp_pos a
  have hxp : Real.exp a ≠ 0 := ne_of_gt hx
  have hsum : 1 + Real.exp a ≠ 0 := by positivity
  field_simp [hxp, hsum]
  ring

theorem one_sub_two_mul_sourceHorizontalProofExchangeDefect_pos (a : ℝ) :
    0 < 1 - 2 * sourceHorizontalProofExchangeDefect a := by
  rw [one_sub_two_mul_sourceHorizontalProofExchangeDefect_eq]
  positivity

/-- Exact nonlinear reconstruction: Gamma curvature is the odds transform of proof exchange. -/
theorem sourceHorizontalGammaSixCurvature_eq_proofExchangeOdds (a : ℝ) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a =
      8 * sourceHorizontalProofExchangeDefect a /
        (1 - 2 * sourceHorizontalProofExchangeDefect a) := by
  apply (eq_div_iff (ne_of_gt
    (one_sub_two_mul_sourceHorizontalProofExchangeDefect_pos a))).2
  exact sourceHorizontalGammaSixCurvature_mul_proofExchangeComplement a

theorem sourceHorizontalProofExchangeDefect_eq_zero_iff (a : ℝ) :
    sourceHorizontalProofExchangeDefect a = 0 ↔ a = 0 := by
  rw [sourceHorizontalProofExchangeDefect, threeSlotExchangeDefect_eq_zero_iff]
  constructor
  · intro h
    exact (logisticPhase_eq_iff a).1 (Subtype.ext h)
  · rintro rfl
    simp

/-- Proof exchange and external completion occupation have the same zero/nonzero phase. -/
theorem routeRExternalTensorCurvature_eq_zero_iff_proofExchangeDefect_eq_zero (a : ℝ) :
    routeRExternalTensorCurvature a = 0 ↔
      sourceHorizontalProofExchangeDefect a = 0 := by
  rw [routeRExternalTensorCurvature_eq_zero_iff,
    sourceHorizontalProofExchangeDefect_eq_zero_iff]

/-- Closed fusion of proof exchange, Gamma cost, and completion occupation. -/
theorem completionProofExchangeCostFusion_law (a : ℝ) :
    (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a *
          (1 - 2 * sourceHorizontalProofExchangeDefect a) =
        8 * sourceHorizontalProofExchangeDefect a) ∧
      0 < 1 - 2 * sourceHorizontalProofExchangeDefect a ∧
      (routeRExternalTensorCurvature a = 0 ↔
        sourceHorizontalProofExchangeDefect a = 0) ∧
      (sourceHorizontalProofExchangeDefect a = 0 ↔ a = 0) := by
  exact ⟨sourceHorizontalGammaSixCurvature_mul_proofExchangeComplement a,
    one_sub_two_mul_sourceHorizontalProofExchangeDefect_pos a,
    routeRExternalTensorCurvature_eq_zero_iff_proofExchangeDefect_eq_zero a,
    sourceHorizontalProofExchangeDefect_eq_zero_iff a⟩

end


end RHTower
