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

theorem nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_below_2365_over_16
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 2365 / 16) :
    (9 / 200000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 2369 / 16
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 2365 / 16 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hw2Lower : (85 : ℝ) ^ 2 < w ^ 2 :=
    pow_lt_pow_left₀ hwLower (by norm_num) (by norm_num)
  have hw2Upper : w ^ 2 < W ^ 2 :=
    pow_lt_pow_left₀ hwUpper hw0.le (by norm_num)
  have huv : u * v < 2365 / 64 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * (2365 / 16) :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = 2365 / 64 := by ring
  have hshape :
      (1600000 : ℝ) * (2365 / 64) <
        200000 * w ^ 2 - 9 * w ^ 4 := by
    by_cases hmid : w ^ 2 ≤ 10000
    · have hfactor : 0 < 200000 - 9 * (w ^ 2 + 7225) := by
        nlinarith
      have hprod :
          0 < (w ^ 2 - 7225) *
            (200000 - 9 * (w ^ 2 + 7225)) :=
        mul_pos (sub_pos.mpr (by
          norm_num at hw2Lower ⊢
          exact hw2Lower)) hfactor
      have hid :
          (200000 * w ^ 2 - 9 * w ^ 4) -
              (200000 * 7225 - 9 * 7225 ^ 2) =
            (w ^ 2 - 7225) *
              (200000 - 9 * (w ^ 2 + 7225)) := by
        ring
      have hend :
          (1600000 : ℝ) * (2365 / 64) <
            200000 * 7225 - 9 * 7225 ^ 2 := by
        norm_num
      nlinarith
    · have hmid' : 10000 < w ^ 2 := lt_of_not_ge hmid
      have hfactor : 0 < 9 * (W ^ 2 + w ^ 2) - 200000 := by
        dsimp only [W]
        nlinarith
      have hprod :
          0 < (W ^ 2 - w ^ 2) *
            (9 * (W ^ 2 + w ^ 2) - 200000) :=
        mul_pos (sub_pos.mpr hw2Upper) hfactor
      have hid :
          (200000 * w ^ 2 - 9 * w ^ 4) -
              (200000 * W ^ 2 - 9 * W ^ 4) =
            (W ^ 2 - w ^ 2) *
              (9 * (W ^ 2 + w ^ 2) - 200000) := by
        ring
      have hend :
          (1600000 : ℝ) * (2365 / 64) <
            200000 * W ^ 2 - 9 * W ^ 4 := by
        norm_num [W]
      rw [← hid] at hprod
      exact hend.trans (sub_pos.mp hprod)
  have hG :
      0 < 200000 * (v ^ 2 - 6 * u * v + u ^ 2) - 9 * w ^ 4 := by
    have hN : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ 2).re =
        (v ^ 2 - 6 * u * v + u ^ 2) / w ^ 4 := by
    rw [pow_two, Complex.mul_re, xiZeroCopyReciprocalSquare_re_formula,
      xiZeroCopyReciprocalSquare_im_formula]
    simp only [u, v, w]
    have hden : u + v ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 200000) (pow_pos hw0 4)]
  nlinarith

/-- No off-critical Xi zero occurs below squared ordinate `2365 / 16`. -/
theorem not_exists_xiZeroCopy_offLine_of_im_sq_lt_2365_over_16 :
    ¬ ∃ q : XiZeroCopy,
      (q.1 : ℂ).re ≠ 1 / 2 ∧
        (q.1 : ℂ).im ^ 2 < 2365 / 16 := by
  rintro ⟨q, hoff, hvUpper⟩
  have huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
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
