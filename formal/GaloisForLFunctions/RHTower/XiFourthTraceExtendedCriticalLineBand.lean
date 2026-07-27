import GaloisForLFunctions.RHTower.XiCenteredOrdersSeventeenEighteenSourcePositivity

/-!
# Extended critical-line band from the fourth reciprocal trace

Exact use of the existing fourth reciprocal-trace source budget extends the unconditional
critical-line band from squared ordinate `295 / 2` to `2365 / 16`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- No off-critical Xi zero occurs below squared ordinate `2365 / 16`. -/
theorem not_exists_xiZeroCopy_offLine_of_im_sq_lt_2365_over_16 :
    ¬ ∃ q : XiZeroCopy,
      (q.1 : ℂ).re ≠ 1 / 2 ∧
        (q.1 : ℂ).im ^ 2 < 2365 / 16 := by
  rintro ⟨q, hoff, hvUpper⟩
  have huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  have huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) :=
    xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hvLower := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hoff
  have hatom :=
    nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_below_2365_over_16
      q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  nlinarith

/-- Every Xi zero copy below squared ordinate `2365 / 16` lies on the critical line. -/
theorem xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16
    (q : XiZeroCopy)
    (hheight : (q.1 : ℂ).im ^ 2 < 2365 / 16) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  exact not_exists_xiZeroCopy_offLine_of_im_sq_lt_2365_over_16
    ⟨q, hoff, hheight⟩

/-- The fourth-trace critical-line band reduces every reciprocal-square transverse square to at
most `1 / 147` of its positive real square. -/
theorem xiThermalOrientationTerm_le_one_over_oneHundredFortySeven_node_sq
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (1 / 147 : ℝ) * xiThermalNode q ^ 2 := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [xiZeroCopyReciprocalSquare_im_formula, hoff]
    norm_num
    positivity
  · let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
    let v : ℝ := (q.1 : ℂ).im ^ 2
    let D : ℝ := (u + v) ^ 2
    have hu0 : 0 ≤ u := by dsimp only [u]; positivity
    have hu : u < 1 / 4 :=
      xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hv : (2365 / 16 : ℝ) ≤ v := by
      apply le_of_not_gt
      intro hvlt
      exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (by
        simpa only [v] using hvlt))
    have hv0 : 0 < v := by nlinarith
    have h590 : 590 * u < v := by nlinarith
    have hprod : 0 ≤ v * (v - 590 * u) :=
      mul_nonneg hv0.le (sub_nonneg.mpr h590.le)
    have hcore : 4 * u * v ≤ (1 / 147 : ℝ) * (v - u) ^ 2 := by
      have hid :
          (v - u) ^ 2 - 147 * (4 * u * v) =
            v * (v - 590 * u) + u ^ 2 := by
        ring
      nlinarith [sq_nonneg u]
    have hD : 0 < D := by dsimp only [D]; positivity
    rw [xiThermalNode, xiZeroCopyReciprocalSquare_re_formula,
      xiZeroCopyReciprocalSquare_im_formula]
    change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
          (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2 ≤
      (1 / 147 : ℝ) *
        (((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) /
          (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2
    rw [show ((q.1 : ℂ).re - 1 / 2) ^ 2 = u by rfl,
      show (q.1 : ℂ).im ^ 2 = v by rfl,
      show (u + v) ^ 2 = D by rfl]
    rw [div_pow, div_pow]
    rw [show (1 / 147 : ℝ) * ((v - u) ^ 2 / D ^ 2) =
        ((1 / 147 : ℝ) * (v - u) ^ 2) / D ^ 2 by ring]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2
    calc
      (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 =
          4 * u * v := by
        dsimp only [u, v]
        ring
      _ ≤ (1 / 147 : ℝ) * (v - u) ^ 2 := hcore

/-- The best endpoint-curvature bound already present in the source corpus improves the universal
off-line squared-height floor to `39537 / 463`. -/
theorem xiZeroCopy_offLine_39537_over_463_lt_im_sq
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    39537 / 463 < (q.1 : ℂ).im ^ 2 := by
  have hbudget :=
    four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hoff
  have hC :=
    xiEndpointCompletedCurvature_lt_fourHundredSixtyThree_over_tenThousand
  nlinarith [sq_nonneg (q.1 : ℂ).im]

end

end RHTower
