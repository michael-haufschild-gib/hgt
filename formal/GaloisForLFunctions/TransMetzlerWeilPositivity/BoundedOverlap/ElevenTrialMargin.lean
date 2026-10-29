import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters

/-!+# A strict scalar margin for a three-conductor eleven-flip trial

The prime-square divisibility profile has mean `101 / 121`. After cancellation
of its first prime excitation, the remaining geometric prime-power cost fits
inside the Robin and pole margin at width ratio `99 / 100`.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory

/-- The plateau's normalized Robin energy has an explicit rational upper bound. -/
theorem plateau_robin_quotient_le :
    bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) ≤ 21 / 20 := by
  have hb := bumpRobin_plateau_le (C := 4) (by norm_num) abs_smoothTransition_sub_le
    etaZero_pos (by norm_num [etaZero])
  have hlog10 : Real.log 10 < (14 : ℝ) / 5 := by
    have h10 : Real.log 10 < Real.log 16 := Real.log_lt_log (by norm_num) (by norm_num)
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith only [h10, h16, Real.log_two_lt_d9]
  have hlog_eta : Real.log etaZero = -3 * Real.log 10 := by
    rw [etaZero, one_div, Real.log_inv,
      show (1000 : ℝ) = 10 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hrobin : bumpRobin transMetzlerProfile 1 ≤ (1045 : ℝ) / 1000 := by
    unfold transMetzlerProfile
    rw [hlog_eta] at hb
    rw [etaZero] at hb ⊢
    norm_num at hb
    linarith only [hb, hlog10]
  rw [div_le_iff₀ integral_transMetzlerProfile_sq_pos]
  linarith only [hrobin, integral_transMetzlerProfile_sq_ge]

private theorem log_two_pi_gt : (9 : ℝ) / 5 < Real.log (2 * Real.pi) := by
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  have he : Real.exp 1 < (68 : ℝ) / 25 := by linarith only [Real.exp_one_lt_d9]
  have hsmall : (6 : ℝ) / 5 ≤ Real.exp (1 / 5) := by
    linarith only [Real.add_one_le_exp (1 / 5 : ℝ)]
  have hproduct : Real.exp (9 / 5 : ℝ) * Real.exp (1 / 5 : ℝ) = Real.exp 1 ^ 2 := by
    rw [← Real.exp_add, sq, ← Real.exp_add]
    norm_num
  have hpi : (31 : ℝ) / 10 < Real.pi := by linarith only [Real.pi_gt_d4]
  have hs := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos (9 / 5 : ℝ)).le
  nlinarith only [he, hproduct, hpi, hs, Real.exp_pos 1]

private theorem log_eleven_lt : Real.log (11 : ℝ) < 5 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) 7)
  norm_num [Finset.sum_range_succ]

/-- Upper cost of all remaining prime powers after the first eleven-power cancellation. -/
def elevenPrimeTailCost : ℝ :=
  4 * Real.log 11 * (2 / (11 : ℝ) ^ 3 + 1 / ((11 : ℝ) ^ 2 * 10))

theorem elevenPrimeTailCost_lt : elevenPrimeTailCost < 1 / 40 := by
  unfold elevenPrimeTailCost
  nlinarith only [log_eleven_lt]

/-- The completed scalar trial bound, retaining its pole charge and all tail costs. -/
def elevenTrialUpperMargin : ℝ :=
  completeWeilSelfFinitePart transMetzlerProfile (99 / 100) +
    completeWeilPoleShift transMetzlerProfile (99 / 100) * (101 / 121 : ℝ) ^ 2 +
    elevenPrimeTailCost

/-- The three-conductor trial's proposed complete-energy upper bound is strictly negative. -/
theorem elevenTrialUpperMargin_neg : elevenTrialUpperMargin < 0 := by
  have hself : completeWeilSelfFinitePart transMetzlerProfile (99 / 100) =
      -Real.log (2 * Real.pi) - Real.log (99 / 100) +
        bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) := by
    rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
      Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) (by norm_num : (99 / 100 : ℝ) ≠ 0)]
    ring
  have hlog : -Real.log (99 / 100 : ℝ) ≤ 1 / 99 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100 / 99)
    rw [show (100 / 99 : ℝ) = (99 / 100 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
    norm_num at h
    exact h
  have hcharge := completeWeilPoleShift_le contDiff_transMetzlerProfile.continuous
    (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos
    (by norm_num : (0 : ℝ) ≤ 99 / 100)
  have hpole : completeWeilPoleShift transMetzlerProfile (99 / 100) * (101 / 121 : ℝ) ^ 2
      ≤ (99 / 100 : ℝ) * (7 / 10) := by
    calc
      _ ≤ (99 / 100 : ℝ) * (101 / 121 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcharge (sq_nonneg _)
      _ ≤ _ := by norm_num
  unfold elevenTrialUpperMargin
  rw [hself]
  linarith only [log_two_pi_gt, hlog, plateau_robin_quotient_le, hpole, elevenPrimeTailCost_lt]

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.elevenTrialUpperMargin_neg
