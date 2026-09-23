import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicSourceRelativeOffsetIncrement

/-!
# Two-offset endpoint debt on literal quantile heads

The positive two-offset affine combination with scales `1/2` and `2` is the
unique positive combination at those scales which cancels the fourth-order
admitted-cell residual.  This file proves its exact source-level cost: it is
the unshifted literal current minus a strictly positive cubic endpoint debt.
Thus it changes no historical prime--polar interaction and cannot be a Route O
producer.
-/

noncomputable section

namespace RHTower

/-- Positive two-offset combination of literal source-relative currents. -/
def ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetCurrent
    (K : ℕ) : ℝ :=
  (16 / 17 : ℝ) *
      ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
        (-2 * Real.log 2) K +
    (1 / 17 : ℝ) *
      ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
        (2 * Real.log 2) K

/-- Literal terminal completion retained by the two physical offsets. -/
def ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpoint
    (K : ℕ) : ℝ :=
  (16 / 17 : ℝ) *
      (Real.exp ((-2 * Real.log 2) / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (4 : ℕ) / 12 +
    (1 / 17 : ℝ) *
      (Real.exp ((2 * Real.log 2) / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (4 : ℕ) / 12

/-- Excess terminal completion over the unshifted literal endpoint. -/
def ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt
    (K : ℕ) : ℝ :=
  (2 / 51 : ℝ) * ccmActualHeadQuantilePolarCoordinate (K + 3) *
    (7 * ccmActualHeadQuantilePolarCoordinate (K + 3) ^ (2 : ℕ) -
      27 * ccmActualHeadQuantilePolarCoordinate (K + 3) + 28)

private theorem ccm_twoOffset_exp_neg :
    Real.exp ((-2 * Real.log 2) / 2) = (1 / 2 : ℝ) := by
  rw [show (-2 * Real.log 2) / 2 = -Real.log 2 by ring,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem ccm_twoOffset_exp_pos :
    Real.exp ((2 * Real.log 2) / 2) = (2 : ℝ) := by
  rw [show (2 * Real.log 2) / 2 = Real.log 2 by ring,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The endpoint correction is exact, not an inequality or a fitted estimate. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpoint_eq_unshifted_add_debt
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpoint K =
      (ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (4 : ℕ) / 12 +
        ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpoint
    ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt
  rw [ccm_twoOffset_exp_neg, ccm_twoOffset_exp_pos]
  ring

/-- The additional endpoint debt is strictly positive on every actual head. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt_pos
    (K : ℕ) :
    0 < ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt
  have hq : 0 < ccmActualHeadQuantilePolarCoordinate (K + 3) := by
    unfold ccmActualHeadQuantilePolarCoordinate
    positivity
  have hquadratic :
      0 < 7 * ccmActualHeadQuantilePolarCoordinate (K + 3) ^ (2 : ℕ) -
        27 * ccmActualHeadQuantilePolarCoordinate (K + 3) + 28 := by
    nlinarith [sq_nonneg (ccmActualHeadQuantilePolarCoordinate (K + 3) - 27 / 14)]
  positivity

/-- The two-offset current is exactly the unshifted literal source current minus its positive
endpoint debt.  In particular it cannot alter the historical prime--polar interaction. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetCurrent_eq_unshifted_sub_debt
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetCurrent K =
      ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent 0 K -
        ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt K := by
  have hminus :=
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic
      (-2 * Real.log 2) K
  have hplus :=
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic
      (2 * Real.log 2) K
  have hzero :=
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic
      0 K
  calc
    ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetCurrent K =
        ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
          ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpoint K := by
      unfold ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetCurrent
        ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpoint
      rw [hminus, hplus]
      ring
    _ = ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
          ((ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (4 : ℕ) / 12 +
            ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt K) := by
      rw [ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpoint_eq_unshifted_add_debt]
    _ = ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent 0 K -
          ccmActualHeadMatchedCompletedQuantileParabolicTwoOffsetEndpointDebt K := by
      simp only [zero_div, Real.exp_zero] at hzero
      rw [hzero]
      ring

end RHTower
