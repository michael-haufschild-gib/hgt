import GaloisForLFunctions.RHTower.LevinsonLinearOptimizationInterior

/-!
# A fixed unconditional admissible Levinson parameter

This file selects one concrete-in-principle mollifier exponent strictly inside
`(0, 1/2)` whose exact Young scalar proportion exceeds `1/3`.  Downstream
analytic modules can target this fixed parameter without carrying an endpoint
limit or adding an admissibility hypothesis.
-/

noncomputable section

namespace RHTower

/-- A fixed mollifier exponent in `(0,1/2)` retaining Young's strict scalar
margin. -/
def levinsonLinearAdmissibleTheta : ℝ :=
  Classical.choose exists_levinsonLinearOptimizationProportion_gt_one_third

theorem levinsonLinearAdmissibleTheta_pos :
    0 < levinsonLinearAdmissibleTheta :=
  (Classical.choose_spec
    exists_levinsonLinearOptimizationProportion_gt_one_third).1

theorem levinsonLinearAdmissibleTheta_lt_half :
    levinsonLinearAdmissibleTheta < 1 / 2 :=
  (Classical.choose_spec
    exists_levinsonLinearOptimizationProportion_gt_one_third).2.1

theorem levinsonLinearAdmissibleTheta_proportion_gt_one_third :
    levinsonLinearOptimizationProportionAt levinsonLinearAdmissibleTheta > 1 / 3 :=
  (Classical.choose_spec
    exists_levinsonLinearOptimizationProportion_gt_one_third).2.2

/-- Young's scalar constant at the fixed admissible exponent. -/
def levinsonLinearAdmissibleConstant : ℝ :=
  levinsonLinearOptimizationConstantAt levinsonLinearAdmissibleTheta

theorem levinsonLinearAdmissibleConstant_pos :
    0 < levinsonLinearAdmissibleConstant :=
  levinsonLinearOptimizationConstantAt_pos levinsonLinearAdmissibleTheta_pos

/-- Exact strict Levinson margin at a fixed exponent satisfying
`0 < theta < 1/2`. -/
theorem one_sub_log_levinsonLinearAdmissibleConstant_div_gt_one_third :
    1 - Real.log levinsonLinearAdmissibleConstant / (13 / 10) > 1 / 3 := by
  simpa only [levinsonLinearOptimizationProportionAt,
    levinsonLinearAdmissibleConstant] using
    levinsonLinearAdmissibleTheta_proportion_gt_one_third

end RHTower
