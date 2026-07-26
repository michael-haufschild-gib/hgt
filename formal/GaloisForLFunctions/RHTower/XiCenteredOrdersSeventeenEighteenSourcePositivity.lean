import GaloisForLFunctions.RHTower.XiCenteredOrdersFifteenSixteenSourcePositivity
import GaloisForLFunctions.RHTower.XiOrderEighteenEdgeCorner

/-!
# Centered orders seventeen and eighteen source positivity

The complete-source fourth-trace budget first forces every Xi zero below squared ordinate
`295/2` onto the critical line. In particular, centered order-eighteen sector failure lies in

`4/25 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 133`,

and centered order-nineteen failure lies in

`7/50 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 295/2`.

Across their union, one fourth reciprocal-trace atom exceeds `9/200000`. Four distinct
FE--Schwarz copies would then exceed the unconditional complete-source upper bound.
Consequently centered reciprocal-square powers eighteen and nineteen have positive real part
atomwise, and normalized prime--archimedean moments seventeen and eighteen are strictly positive.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

theorem nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_of_centered_orderNineteenRange
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 295 / 2) :
    (9 / 200000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 591 / 4
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 295 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hw2Lower : (85 : ℝ) ^ 2 < w ^ 2 :=
    pow_lt_pow_left₀ hwLower (by norm_num) (by norm_num)
  have hw2Upper : w ^ 2 < W ^ 2 :=
    pow_lt_pow_left₀ hwUpper hw0.le (by norm_num)
  have huv : u * v < 295 / 8 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * (295 / 2) :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = 295 / 8 := by ring
  have hshape :
      (1600000 : ℝ) * (295 / 8) <
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
          (1600000 : ℝ) * (295 / 8) <
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
          (1600000 : ℝ) * (295 / 8) <
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

theorem not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner :
    ¬ ∃ q : XiZeroCopy,
      (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 295 / 2 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    intro h
    rw [h] at huLower
    norm_num at huLower
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hoff
  have hatom :=
    nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_of_centered_orderNineteenRange
      q (by linarith [huLower]) huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  nlinarith

/-- No off-critical Xi zero occurs below squared ordinate `295/2`. -/
theorem not_exists_xiZeroCopy_offLine_of_im_sq_lt_twoHundredNinetyFiveHalves :
    ¬ ∃ q : XiZeroCopy,
      (q.1 : ℂ).re ≠ 1 / 2 ∧
        (q.1 : ℂ).im ^ 2 < 295 / 2 := by
  rintro ⟨q, hoff, hvUpper⟩
  have huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvLower := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hoff
  have hatom :=
    nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_of_centered_orderNineteenRange
      q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  nlinarith

/-- Every Xi zero copy below squared ordinate `295/2` lies on the critical line. -/
theorem xiZeroCopy_re_eq_half_of_im_sq_lt_twoHundredNinetyFiveHalves
    (q : XiZeroCopy)
    (hheight : (q.1 : ℂ).im ^ 2 < 295 / 2) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  exact not_exists_xiZeroCopy_offLine_of_im_sq_lt_twoHundredNinetyFiveHalves
    ⟨q, hoff, hheight⟩

theorem xiCenteredOrderEighteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (4 / 25 : ℝ)) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 4 / 25 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hA : 2121 / 25 < A := by dsimp only [A]; nlinarith
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 132 * B ^ 2 ≤ (2112 / 25 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hvA : v ≤ A + 4 / 25 := by dsimp only [A]; nlinarith
  have hbase :
      (2112 / 25 : ℝ) * (2121 / 25 + 4 / 25) <
        (2121 / 25 : ℝ) ^ 2 := by
    norm_num
  have hprod :
      0 < (A - 2121 / 25) *
        (A + 2121 / 25 - 2112 / 25) := by
    apply mul_pos
    · nlinarith
    · nlinarith
  have hpoly : (2112 / 25 : ℝ) * (A + 4 / 25) < A ^ 2 := by
    nlinarith
  change 132 * B ^ 2 < A ^ 2
  nlinarith

theorem xiCenteredOrderEighteenSectorRatio_of_oneHundredThirtyThree_le_im_sq
    (q : XiZeroCopy) (hhigh : 133 ≤ (q.1 : ℂ).im ^ 2) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 133 ≤ v := by simpa only [v] using hhigh
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 132 * B ^ 2 < 132 * v := by rw [hB]; nlinarith
  have hbase : 132 * v < (v - 1 / 4) ^ 2 := by
    have hprod : 0 ≤ (v - 133) * v :=
      mul_nonneg (sub_nonneg.mpr hv) (by positivity)
    nlinarith
  have hA0 : 0 < A := by dsimp only [A]; nlinarith
  have hleft : 0 < v - 1 / 4 := by nlinarith
  have hlt : v - 1 / 4 < A := by dsimp only [A]; nlinarith
  have hAsq : (v - 1 / 4) ^ 2 < A ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hleft hA0)]
  change 132 * B ^ 2 < A ^ 2
  linarith

theorem xiCenteredOrderEighteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 133 := by
  have hedge : (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    linarith [xiCenteredOrderEighteenSectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 133 := by
    by_contra h
    linarith [xiCenteredOrderEighteenSectorRatio_of_oneHundredThirtyThree_le_im_sq
      q (le_of_not_gt h)]
  exact ⟨hedge, hu, hvlow, hvhigh⟩

theorem xiZeroCopyReciprocalSquare_pow_eighteen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 18).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  change 0 < ((((A : ℂ) - B * I)⁻¹) ^ 18).re
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
    apply orderEighteenReciprocalPower_re_pos_of_sectorRatio hA
    dsimp only [A, B]
    rw [hoff]
    norm_num
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  · by_contra hnot
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
    have hA : 0 < A := by dsimp only [A]; nlinarith
    have hfail : A ^ 2 ≤ 132 * B ^ 2 := by
      by_contra h
      have hpos :=
        orderEighteenReciprocalPower_re_pos_of_sectorRatio hA (lt_of_not_ge h)
      have hnonpos : ((((A : ℂ) - B * I)⁻¹) ^ 18).re ≤ 0 :=
        le_of_not_gt hnot
      linarith
    have hc := xiCenteredOrderEighteenSectorFailure_mem_edgeCorner q hoff
      (by simpa only [A, B] using hfail)
    exact not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner
      ⟨q, by linarith [hc.1], hc.2.1, hc.2.2.1,
        hc.2.2.2.trans (by norm_num)⟩

theorem xiCenteredOrderNineteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (7 / 50 : ℝ)) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 7 / 50 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hA : 4243 / 50 < A := by dsimp only [A]; nlinarith
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 147 * B ^ 2 ≤ (2058 / 25 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hvA : v ≤ A + 7 / 50 := by dsimp only [A]; nlinarith
  have hbase :
      (2058 / 25 : ℝ) * (4243 / 50 + 7 / 50) <
        (4243 / 50 : ℝ) ^ 2 := by
    norm_num
  have hprod :
      0 < (A - 4243 / 50) *
        (A + 4243 / 50 - 2058 / 25) := by
    apply mul_pos
    · nlinarith
    · nlinarith
  have hpoly : (2058 / 25 : ℝ) * (A + 7 / 50) < A ^ 2 := by
    nlinarith
  change 147 * B ^ 2 < A ^ 2
  nlinarith

theorem xiCenteredOrderNineteenSectorRatio_of_twoHundredNinetyFiveHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 295 / 2 ≤ (q.1 : ℂ).im ^ 2) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 295 / 2 ≤ v := by simpa only [v] using hhigh
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 147 * B ^ 2 < 147 * v := by rw [hB]; nlinarith
  have hbase : 147 * v < (v - 1 / 4) ^ 2 := by
    have hprod : 0 ≤ (v - 295 / 2) * v :=
      mul_nonneg (sub_nonneg.mpr hv) (by positivity)
    nlinarith
  have hA0 : 0 < A := by dsimp only [A]; nlinarith
  have hleft : 0 < v - 1 / 4 := by nlinarith
  have hlt : v - 1 / 4 < A := by dsimp only [A]; nlinarith
  have hAsq : (v - 1 / 4) ^ 2 < A ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hleft hA0)]
  change 147 * B ^ 2 < A ^ 2
  linarith

theorem xiCenteredOrderNineteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 295 / 2 := by
  have hedge : (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    linarith [xiCenteredOrderNineteenSectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 295 / 2 := by
    by_contra h
    linarith [xiCenteredOrderNineteenSectorRatio_of_twoHundredNinetyFiveHalves_le_im_sq
      q (le_of_not_gt h)]
  exact ⟨hedge, hu, hvlow, hvhigh⟩

theorem xiZeroCopyReciprocalSquare_pow_nineteen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 19).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  change 0 < ((((A : ℂ) - B * I)⁻¹) ^ 19).re
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
    apply orderNineteenReciprocalPower_re_pos_of_sectorRatio hA
    dsimp only [A, B]
    rw [hoff]
    norm_num
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  · by_contra hnot
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
    have hA : 0 < A := by dsimp only [A]; nlinarith
    have hfail : A ^ 2 ≤ 147 * B ^ 2 := by
      by_contra h
      have hpos :=
        orderNineteenReciprocalPower_re_pos_of_sectorRatio hA (lt_of_not_ge h)
      have hnonpos : ((((A : ℂ) - B * I)⁻¹) ^ 19).re ≤ 0 :=
        le_of_not_gt hnot
      linarith
    have hc := xiCenteredOrderNineteenSectorFailure_mem_edgeCorner q hoff
      (by simpa only [A, B] using hfail)
    exact not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner ⟨q, hc⟩

theorem normalizedPrimeArchMoment_seventeen_pos :
    0 < normalizedPrimeArchMoment 17 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 17
  simpa using xiZeroCopyReciprocalSquare_pow_eighteen_re_pos

theorem normalizedPrimeArchMoment_eighteen_pos :
    0 < normalizedPrimeArchMoment 18 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 18
  simpa using xiZeroCopyReciprocalSquare_pow_nineteen_re_pos

end

end RHTower
