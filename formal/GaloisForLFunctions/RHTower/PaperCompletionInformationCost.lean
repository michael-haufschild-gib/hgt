import GaloisForLFunctions.HTGeometry.PaperLogisticExchangeScaling
import GaloisForLFunctions.RHTower.CompletionProofExchangeCostFusion

/-! # Information cost of constitutive completion and its diffusive limit

The paper's logistic relative entropy measures the native proof-exchange defect and
obeys an exact algebraic identity with Gamma-six curvature. For vanishing grades and
quadratically increasing depth, exchange work tends to one eighth while both information
work and Gamma work tend to one. Thus nonzero total work survives a neutral pointwise limit.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry Filter
open scoped Topology

/-- Native exchange defect is controlled by the proven paper Pinsker inequality. -/
theorem paperCompletionExchangeDefect_le_information (a : ℝ) :
    4 * sourceHorizontalProofExchangeDefect a ≤ paperLogisticExchangeInformation a := by
  rw [sourceHorizontalProofExchangeDefect, threeSlotExchangeDefect_eq]
  linarith [paperLogisticExchangeInformation_contrast_bound a]

/-- Squared information is exactly the native exchange defect times the squared grade. -/
theorem paperCompletionInformation_sq (a : ℝ) :
    paperLogisticExchangeInformation a ^ 2 =
      8 * a ^ 2 * sourceHorizontalProofExchangeDefect a := by
  rw [paperLogisticExchangeInformation_eq, sourceHorizontalProofExchangeDefect,
    threeSlotExchangeDefect_eq]
  ring

/-- An unconditional identity ties paper information directly to the native Gamma curvature. -/
theorem paperCompletionInformation_gamma_identity (a : ℝ) :
    paperLogisticExchangeInformation a ^ 2 *
        (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a + 4) =
      4 * a ^ 2 * sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
  have hf : 2 * sourceHorizontalProofExchangeDefect a *
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a + 4) =
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
    nlinarith [sourceHorizontalGammaSixCurvature_mul_proofExchangeComplement a]
  rw [paperCompletionInformation_sq]
  calc
    _ = 4 * a ^ 2 * (2 * sourceHorizontalProofExchangeDefect a *
        (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a + 4)) := by ring
    _ = _ := by rw [hf]

theorem paperCompletionInformation_eq_zero_iff_exchange (a : ℝ) :
    paperLogisticExchangeInformation a = 0 ↔ sourceHorizontalProofExchangeDefect a = 0 := by
  rw [paperLogisticExchangeInformation_eq_zero_iff, sourceHorizontalProofExchangeDefect_eq_zero_iff]

/-- Every finite grade in the diffusive family remains nonneutral. -/
theorem paperCompletionDiffusiveInformation_pos (n : ℕ) :
    0 < paperLogisticExchangeInformation (paperLogisticDiffusiveGrade n) := by
  refine lt_of_le_of_ne (paperLogisticExchangeInformation_nonneg _) ?_
  intro h
  exact (paperLogisticDiffusiveGrade_pos n).ne'
    ((paperLogisticExchangeInformation_eq_zero_iff _).mp h.symm)

/-- Vanishing individual proof-exchange defects. -/
theorem paperCompletionDiffusiveExchange_tendsto_zero :
    Tendsto (fun n : ℕ => sourceHorizontalProofExchangeDefect (paperLogisticDiffusiveGrade n))
      atTop (𝓝 0) := by
  have hc : Continuous (fun a : ℝ => (Real.exp a - 1) / (Real.exp a + 1)) :=
    (Real.continuous_exp.sub continuous_const).div
      (Real.continuous_exp.add continuous_const) (fun _ => by positivity)
  have ht : Tendsto (fun n : ℕ =>
      (logisticPhase (paperLogisticDiffusiveGrade n) : ℝ) -
        (logisticPhase (-paperLogisticDiffusiveGrade n) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, paperLogisticContrast_eq, Real.exp_zero, sub_self, zero_div] using
      hc.continuousAt.tendsto.comp paperLogisticDiffusiveGrade_tendsto
  simpa only [sourceHorizontalProofExchangeDefect, threeSlotExchangeDefect_eq,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] using
    (ht.pow 2).div_const 2

/-- Quadratic depth leaves precisely one eighth unit of total exchange defect. -/
theorem paperCompletionDiffusiveExchange_work_limit :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
      sourceHorizontalProofExchangeDefect (paperLogisticDiffusiveGrade n)) atTop (𝓝 (1 / 8)) := by
  have h := (paperLogisticDiffusiveContrast_tendsto.pow 2).div_const 2
  convert h using 1
  · ext n
    rw [sourceHorizontalProofExchangeDefect, threeSlotExchangeDefect_eq]
    ring
  · congr 1
    norm_num

/-- The same grades have a unit total Gamma-six cost in the limit. -/
theorem paperCompletionDiffusiveGamma_work_limit :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (paperLogisticDiffusiveGrade n))
      atTop (𝓝 1) := by
  have hn := (tendsto_const_nhds (x := (8 : ℝ))).mul
    paperCompletionDiffusiveExchange_work_limit
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul paperCompletionDiffusiveExchange_tendsto_zero)
  have h := hn.div hd (by norm_num)
  convert h using 1
  · ext n
    change ((n : ℝ) + 1) ^ 2 *
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (paperLogisticDiffusiveGrade n) =
      (8 * (((n : ℝ) + 1) ^ 2 *
        sourceHorizontalProofExchangeDefect (paperLogisticDiffusiveGrade n))) /
        (1 - 2 * sourceHorizontalProofExchangeDefect (paperLogisticDiffusiveGrade n))
    rw [sourceHorizontalGammaSixCurvature_eq_proofExchangeOdds]
    ring
  · congr 1
    norm_num

end
end RHTower
