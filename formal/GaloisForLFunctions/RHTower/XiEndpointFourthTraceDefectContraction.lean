import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand
import GaloisForLFunctions.RHTower.XiEndpointQuantitativeNormBudget

/-!
# Fourth-trace contraction of the Xi endpoint reflection defect

The endpoint reflection-defect atom vanishes exactly on the critical line.  Its nonzero support is
therefore confined to off-line Xi copies, where the fourth reciprocal-trace theorem supplies the
much stronger squared-height floor `2365 / 16`.  Combining the two facts improves the global defect
bound to

`xiEndpointReflectionDefectEnergy ≤ (16 / 2365) * xiEndpointCompletedCurvature`

and the endpoint Hermitian/source ratio to `2373 / 2365`.

This is an unconditional quantitative contraction.  Its vanishing, not merely its smallness,
remains equivalent to RH.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- An off-line squared-height floor `K` bounds its endpoint reflection-defect atom by `1 / K`
times its positive endpoint cross charge. -/
theorem endpoint_defect_term_le_inv_height_mul_cross_of_offLine
    {K : ℝ} (hK : 0 < K) (q : XiZeroCopy)
    (_hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hheight : K ≤ (q.1 : ℂ).im ^ 2) :
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ 2 ≤
      (1 / K) * xiEndpointCrossCharge q := by
  rw [endpoint_defect_term_eq, xiEndpointCrossCharge, endpoint_cross_term_re_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hApos : 0 < (q.1 : ℂ).re ^ 2 + (q.1 : ℂ).im ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hBpos : 0 < (1 - (q.1 : ℂ).re) ^ 2 + (q.1 : ℂ).im ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hdenpos : 0 <
      ((q.1 : ℂ).re ^ 2 + (q.1 : ℂ).im ^ 2) *
        ((1 - (q.1 : ℂ).re) ^ 2 + (q.1 : ℂ).im ^ 2) :=
    mul_pos hApos hBpos
  rw [div_le_iff₀ hdenpos]
  field_simp [ne_of_gt hK]
  nlinarith [sq_nonneg (1 - 2 * (q.1 : ℂ).re),
    mul_nonneg hstrip.1.le (sub_nonneg.mpr hstrip.2.le)]

/-- Fourth-trace critical-line localization gives the sharp available pointwise defect/cross
coefficient `16 / 2365` for every Xi copy. -/
theorem endpoint_defect_term_le_sixteen_over_twoThousandThreeHundredSixtyFive_mul_cross
    (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ 2 ≤
      (16 / 2365 : ℝ) * xiEndpointCrossCharge q := by
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have hzero :
        ‖xiRawReciprocalCoordinate q -
          xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ 2 = 0 := by
      rw [endpoint_defect_term_eq, hon]
      norm_num
    rw [hzero]
    exact mul_nonneg (by norm_num)
      (by simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q)
  · have hheight : (2365 / 16 : ℝ) ≤ (q.1 : ℂ).im ^ 2 := by
      apply le_of_not_gt
      intro hlt
      exact hon (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hlt)
    have h := endpoint_defect_term_le_inv_height_mul_cross_of_offLine
      (K := 2365 / 16) (by norm_num) q hon hheight
    norm_num at h ⊢
    exact h

/-- **Unconditional fourth-trace endpoint-defect contraction.** -/
theorem xiEndpointReflectionDefectEnergy_le_sixteen_over_twoThousandThreeHundredSixtyFive_mul_curvature :
    xiEndpointReflectionDefectEnergy ≤
      (16 / 2365 : ℝ) * xiEndpointCompletedCurvature := by
  have hscaled := summable_xiEndpointCrossCharge.mul_left (16 / 2365 : ℝ)
  have hsumle := summable_xiEndpointReflectionDefectEnergy.tsum_le_tsum
    endpoint_defect_term_le_sixteen_over_twoThousandThreeHundredSixtyFive_mul_cross
    hscaled
  rw [xiEndpointReflectionDefectEnergy]
  calc
    _ ≤ ∑' q : XiZeroCopy, (16 / 2365 : ℝ) * xiEndpointCrossCharge q := hsumle
    _ = (16 / 2365 : ℝ) * ∑' q : XiZeroCopy, xiEndpointCrossCharge q :=
      tsum_mul_left
    _ = (16 / 2365 : ℝ) * xiEndpointCompletedCurvature := by
      rw [tsum_xiEndpointCrossCharge_eq_curvature]

/-- **Unconditional fourth-trace endpoint norm budget.**  The raw Hermitian mass is at most
`2373 / 2365` times the holomorphic endpoint curvature. -/
theorem xiRawReciprocalHermitianMass_le_twoThousandThreeHundredSeventyThree_over_twoThousandThreeHundredSixtyFive_mul_curvature :
    xiRawReciprocalHermitianMass ≤
      (2373 / 2365 : ℝ) * xiEndpointCompletedCurvature := by
  have hdef :=
    xiEndpointReflectionDefectEnergy_le_sixteen_over_twoThousandThreeHundredSixtyFive_mul_curvature
  have hid := xiEndpointReflectionDefectEnergy_eq_mass_sub_source
  calc
    xiRawReciprocalHermitianMass =
        xiEndpointCompletedCurvature + xiEndpointReflectionDefectEnergy / 2 := by
      linarith
    _ ≤ xiEndpointCompletedCurvature +
        ((16 / 2365 : ℝ) * xiEndpointCompletedCurvature) / 2 := by
      linarith
    _ = (2373 / 2365 : ℝ) * xiEndpointCompletedCurvature := by ring

end

end RHTower
