import GaloisForLFunctions.RHTower.CCMQuantileExponentialRampDeficit
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Centered age and the signed bulk remainder

The exponential-ramp current separates into a centered-age force, a globally
nonpositive bulk remainder, and the exact oriented terminal current. The age
force is the time derivative of the literal position field at fixed head.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmExponentialRampBulkMassField (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r*Real.exp ((Real.log n-T)/2)

def ccmExponentialRampCenteredBulkField (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmActualHeadExponentialRampPositionField T N r-2*ccmExponentialRampBulkMassField T N r

def ccmExponentialRampSecondOrderWeight (r : ℝ) : ℝ :=
  2*ccmExponentialRampDisplacementWeight r+ccmExponentialRampDerivativeWeight r

theorem ccmExponentialRampBulkMassField_nonneg (T : ℝ) (N : ℕ) (r : ℝ) :
    0 ≤ ccmExponentialRampBulkMassField T N r :=
  Finset.sum_nonneg fun n _ => mul_nonneg (ccmOutgoingQuantileDisplacementCellDensity_nonneg n r)
    (Real.exp_pos _).le

/-- Convexity of the exponential gives a globally signed remainder coefficient. -/
theorem ccmExponentialRampSecondOrderWeight_nonpos (r : ℝ) :
    ccmExponentialRampSecondOrderWeight r ≤ 0 := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-r/2)) (Real.exp_pos (r/2)).le
  rw [← Real.exp_add, show -r/2+r/2 = 0 by ring, Real.exp_zero] at h
  unfold ccmExponentialRampSecondOrderWeight ccmExponentialRampDisplacementWeight ccmExponentialRampDerivativeWeight
  nlinarith only [h]

@[simp] theorem ccmExponentialRampSecondOrderWeight_zero : ccmExponentialRampSecondOrderWeight 0 = 0 := by
  simp [ccmExponentialRampSecondOrderWeight, ccmExponentialRampDisplacementWeight, ccmExponentialRampDerivativeWeight]

theorem hasDerivAt_ccmExponentialRampSecondOrderWeight (r : ℝ) :
    HasDerivAt ccmExponentialRampSecondOrderWeight (-r/2*Real.exp (r/2)) r := by
  have he := ((hasDerivAt_id r).div_const 2).exp
  have h := (he.sub_const 1).const_mul 2 |>.add (((hasDerivAt_id r).neg).mul he)
  convert! h using 1
  · rfl
  · simp only [id_eq]
    ring

/-- After centering, the bulk mass coefficient is quadratically small at zero displacement. -/
theorem abs_ccmExponentialRampSecondOrderWeight_le (r : ℝ) :
    |ccmExponentialRampSecondOrderWeight r| ≤ (r^2/2)*Real.exp (|r|/2) := by
  have hb (s : ℝ) (hs : s ∈ Set.Icc (-|r|) |r|) :
      ‖-s/2*Real.exp (s/2)‖ ≤ (|r|/2)*Real.exp (|r|/2) := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (div_le_div_of_nonneg_right (abs_le.mpr hs) (by norm_num))
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hs.2 (by norm_num))) (Real.exp_pos _).le (by positivity)
  have h := (convex_Icc (-|r|) |r|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hasDerivAt_ccmExponentialRampSecondOrderWeight s).hasDerivWithinAt) hb
    (show (0 : ℝ) ∈ Set.Icc (-|r|) |r| from ⟨neg_nonpos.mpr (abs_nonneg r), abs_nonneg r⟩)
    (show r ∈ Set.Icc (-|r|) |r| from ⟨neg_abs_le r, le_abs_self r⟩)
  calc
    _ ≤ ((|r|/2)*Real.exp (|r|/2))*|r| := by
      simpa only [ccmExponentialRampSecondOrderWeight_zero, sub_zero, Real.norm_eq_abs] using h
    _ = _ := by rw [← sq_abs r]; ring

theorem abs_ccmExponentialRampBulkRemainder_le (T : ℝ) (N : ℕ) (r : ℝ) :
    |ccmExponentialRampSecondOrderWeight r*ccmExponentialRampBulkMassField T N r| ≤
      ((r^2/2)*Real.exp (|r|/2))*ccmExponentialRampBulkMassField T N r := by
  rw [abs_mul, abs_of_nonneg (ccmExponentialRampBulkMassField_nonneg T N r)]
  exact mul_le_mul_of_nonneg_right (abs_ccmExponentialRampSecondOrderWeight_le r)
    (ccmExponentialRampBulkMassField_nonneg T N r)

theorem ccmExponentialRampCurrent_eq_centeredAge_bulk_terminal (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r =
      ccmExponentialRampDisplacementWeight r*ccmExponentialRampCenteredBulkField T N r +
        ccmExponentialRampSecondOrderWeight r*ccmExponentialRampBulkMassField T N r +
          ccmExponentialRampDerivativeWeight r*ccmActualHeadQuantileTerminalDisplacementDensity T N r := by
  rw [ccmActualHeadExponentialRampCurrent_eq_two_fields]
  unfold ccmExponentialRampCenteredBulkField ccmExponentialRampSecondOrderWeight
    ccmActualHeadExponentialRampMassField ccmExponentialRampBulkMassField
  ring

/-- The exponentially centered age is the exact fixed-head time force. -/
theorem hasDerivAt_ccmExponentialRampPositionField_time (T : ℝ) (N : ℕ) (r : ℝ) :
    HasDerivAt (fun t => ccmActualHeadExponentialRampPositionField t N r)
      (ccmExponentialRampBulkMassField T N r-(1/2 : ℝ)*ccmActualHeadExponentialRampPositionField T N r) T := by
  have hd (n : ℕ) : HasDerivAt
      (fun t : ℝ => ccmOutgoingQuantileDisplacementCellDensity n r*Real.exp ((Real.log n-t)/2)*(t-Real.log n))
      (ccmOutgoingQuantileDisplacementCellDensity n r*Real.exp ((Real.log n-T)/2) -
        (1/2 : ℝ)*(ccmOutgoingQuantileDisplacementCellDensity n r*Real.exp ((Real.log n-T)/2)*(T-Real.log n))) T := by
    have he := (((hasDerivAt_id T).const_sub (Real.log n)).div_const 2).exp
    convert! (he.const_mul (ccmOutgoingQuantileDisplacementCellDensity n r)).mul
      ((hasDerivAt_id T).sub_const (Real.log n)) using 1
    simp only [id_eq]
    ring
  have h := HasDerivAt.fun_sum (u := Finset.range N) (fun n _ => hd n)
  simpa only [ccmActualHeadExponentialRampPositionField, ccmExponentialRampBulkMassField,
    Finset.sum_sub_distrib, Finset.mul_sum] using h

theorem ccmExponentialRampCenteredBulkField_eq_timeForce (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmExponentialRampCenteredBulkField T N r =
      -2*deriv (fun t => ccmActualHeadExponentialRampPositionField t N r) T := by
  rw [(hasDerivAt_ccmExponentialRampPositionField_time T N r).deriv]
  unfold ccmExponentialRampCenteredBulkField
  ring

theorem ccmExponentialRampCurrent_eq_timeForce_remainder_terminal (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r =
      -2*ccmExponentialRampDisplacementWeight r*
        deriv (fun t => ccmActualHeadExponentialRampPositionField t N r) T +
      ccmExponentialRampSecondOrderWeight r*ccmExponentialRampBulkMassField T N r +
        ccmExponentialRampDerivativeWeight r*ccmActualHeadQuantileTerminalDisplacementDensity T N r := by
  rw [ccmExponentialRampCurrent_eq_centeredAge_bulk_terminal, ccmExponentialRampCenteredBulkField_eq_timeForce]
  ring

/-- The full signed bulk current is bounded above by its age force; the terminal remains explicit. -/
theorem ccmExponentialRampCurrent_sub_terminal_le_timeForce (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r -
      ccmExponentialRampDerivativeWeight r*ccmActualHeadQuantileTerminalDisplacementDensity T N r ≤
        -2*ccmExponentialRampDisplacementWeight r*
          deriv (fun t => ccmActualHeadExponentialRampPositionField t N r) T := by
  rw [ccmExponentialRampCurrent_eq_timeForce_remainder_terminal]
  have h := mul_nonpos_of_nonpos_of_nonneg (ccmExponentialRampSecondOrderWeight_nonpos r)
    (ccmExponentialRampBulkMassField_nonneg T N r)
  linarith only [h]

end RHTower
