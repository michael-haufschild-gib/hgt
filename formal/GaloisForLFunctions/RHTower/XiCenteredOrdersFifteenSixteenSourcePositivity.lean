import GaloisForLFunctions.RHTower.XiCenteredOrderFourteenSourcePositivity
import GaloisForLFunctions.RHTower.XiOrderFifteenEdgeCorner
import GaloisForLFunctions.RHTower.XiOrderSixteenCornerSourceExclusion

/-!
# Centered orders fifteen and sixteen source positivity

The centered order-sixteen and order-seventeen sector failures lie inside

`1/6 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 119`.

Throughout this corner, one fourth reciprocal-trace atom exceeds `1/20000`.  Four distinct
FE--Schwarz copies would therefore exceed the unconditional complete-source upper bound.
Consequently centered reciprocal-square powers sixteen and seventeen have positive real part
atomwise, and normalized prime--archimedean moments fifteen and sixteen are strictly positive.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Four distinct FE--Schwarz copies of an off-line zero contribute at most the complete
nonnegative fourth reciprocal trace. -/
theorem four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 * (xiZeroCopyReciprocalSquare q ^ 2).re ≤
      normalizedPrimeArchMoment 1 := by
  let qJ := xiZeroCopyLineConjEquiv q
  let qC := xiZeroCopyConjEquiv q
  let qCJ := xiZeroCopyLineConjEquiv qC
  let s : Finset XiZeroCopy := {q, qJ, qC, qCJ}
  have hqJ : q ≠ qJ := by
    simpa only [qJ] using xiZeroCopy_ne_lineConj_of_re_ne_half q hoff
  have hqC : q ≠ qC := by
    simpa only [qC] using xiZeroCopy_ne_conj q
  have hqCJ : q ≠ qCJ := by
    simpa only [qC, qCJ] using xiZeroCopy_ne_lineConjConj q
  have hqJqC : qJ ≠ qC := by
    simpa only [qJ, qC] using xiZeroCopy_lineConj_ne_conj q
  have hqJqCJ : qJ ≠ qCJ := by
    simpa only [qJ, qC, qCJ] using xiZeroCopy_lineConj_ne_lineConjConj q
  have hqCqCJ : qC ≠ qCJ := by
    simpa only [qC, qCJ] using
      xiZeroCopy_conj_ne_lineConjConj_of_re_ne_half q hoff
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ 2).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := hsum.sum_le_tsum s (fun r _ => xiFourthReciprocalTraceAtom_nonneg r)
  have hJ : (xiZeroCopyReciprocalSquare qJ ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
    simpa only [qJ] using xiFourthReciprocalTraceAtom_lineConj q
  have hCq : (xiZeroCopyReciprocalSquare qC ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
    simpa only [qC] using xiFourthReciprocalTraceAtom_conj q
  have hCJ : (xiZeroCopyReciprocalSquare qCJ ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
    calc
      (xiZeroCopyReciprocalSquare qCJ ^ 2).re =
          (xiZeroCopyReciprocalSquare qC ^ 2).re := by
        simpa only [qC, qCJ] using xiFourthReciprocalTraceAtom_lineConj qC
      _ = (xiZeroCopyReciprocalSquare q ^ 2).re := hCq
  have hfinite :
      ∑ r ∈ s, (xiZeroCopyReciprocalSquare r ^ 2).re =
        4 * (xiZeroCopyReciprocalSquare q ^ 2).re := by
    simp only [s]
    rw [Finset.sum_insert (by simp [hqJ, hqC, hqCJ]),
      Finset.sum_insert (by simp [hqJqC, hqJqCJ]),
      Finset.sum_insert (by simp [hqCqCJ]), Finset.sum_singleton,
      hJ, hCq, hCJ]
    ring
  rw [hfinite, tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
  exact hle

/-- Across the complete centered order-seventeen failure range, every fourth reciprocal-trace
atom exceeds `1/20000`. -/
theorem one_over_twentyThousand_lt_xiFourthReciprocalTraceAtom_of_centered_orderSeventeenRange
    (q : XiZeroCopy)
    (huLower : (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 119) :
    (1 / 20000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 477 / 4
  have hu0 : 0 < u := by
    exact (by norm_num : (0 : ℝ) < 1 / 6).trans
      (by simpa only [u] using huLower)
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 119 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hw2Lower : (85 : ℝ) ^ 2 < w ^ 2 :=
    pow_lt_pow_left₀ hwLower (by norm_num) (by norm_num)
  have hw2Upper : w ^ 2 < W ^ 2 :=
    pow_lt_pow_left₀ hwUpper hw0.le (by norm_num)
  have huv : u * v < 119 / 4 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right (by simpa only [u] using huUpper) hv0
      _ < (1 / 4 : ℝ) * 119 :=
        mul_lt_mul_of_pos_left (by simpa only [v] using hvUpper) (by norm_num)
      _ = 119 / 4 := by ring
  have hshape : (4760000 : ℝ) < 20000 * w ^ 2 - w ^ 4 := by
    by_cases hmid : w ^ 2 ≤ 10000
    · have hfactor : 0 < 12775 - w ^ 2 := by nlinarith
      have hprod : 0 < (w ^ 2 - 7225) * (12775 - w ^ 2) :=
        mul_pos (sub_pos.mpr (by
          norm_num at hw2Lower ⊢
          exact hw2Lower)) hfactor
      have hid :
          (20000 * w ^ 2 - w ^ 4) -
              (20000 * 7225 - 7225 ^ 2) =
            (w ^ 2 - 7225) * (12775 - w ^ 2) := by
        ring
      norm_num at hid ⊢
      nlinarith
    · have hmid' : 10000 < w ^ 2 := lt_of_not_ge hmid
      have hfactor : 0 < w ^ 2 + W ^ 2 - 20000 := by
        dsimp only [W]
        nlinarith
      have hprod : 0 < (W ^ 2 - w ^ 2) * (w ^ 2 + W ^ 2 - 20000) :=
        mul_pos (sub_pos.mpr hw2Upper) hfactor
      have hid :
          (20000 * w ^ 2 - w ^ 4) -
              (20000 * W ^ 2 - W ^ 4) =
            (W ^ 2 - w ^ 2) * (w ^ 2 + W ^ 2 - 20000) := by
        ring
      have hend : (4760000 : ℝ) <
          20000 * W ^ 2 - W ^ 4 := by
        norm_num [W]
      nlinarith
  have hG :
      0 < 20000 * (v ^ 2 - 6 * u * v + u ^ 2) - w ^ 4 := by
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
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 20000) (pow_pos hw0 4)]
  nlinarith

/-- The complete centered order-seventeen source corner is empty. -/
theorem not_exists_xiZeroCopy_mem_centeredOrderSeventeen_sourceCorner :
    ¬ ∃ q : XiZeroCopy,
      (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 119 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    intro h
    rw [h] at huLower
    norm_num at huLower
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hoff
  have hatom :=
    one_over_twentyThousand_lt_xiFourthReciprocalTraceAtom_of_centered_orderSeventeenRange
      q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  nlinarith

/-! ### Centered order sixteen -/

theorem xiCenteredOrderSixteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 6 : ℝ)) :
    104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 1 / 6 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hA : 509 / 6 < A := by dsimp only [A]; nlinarith
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 104 * B ^ 2 ≤ (208 / 3 : ℝ) * v := by rw [hB]; nlinarith
  have hfactor : 0 < A + 509 / 6 - 208 / 3 := by nlinarith
  have hprod : 0 < (A - 509 / 6) * (A + 509 / 6 - 208 / 3) :=
    mul_pos (sub_pos.mpr hA) hfactor
  have hpoly : (208 / 3 : ℝ) * (A + 1 / 6) < A ^ 2 := by nlinarith
  have hvA : v ≤ A + 1 / 6 := by dsimp only [A]; nlinarith
  change 104 * B ^ 2 < A ^ 2
  nlinarith

theorem xiCenteredOrderSixteenSectorRatio_of_oneHundredFive_le_im_sq
    (q : XiZeroCopy) (hhigh : 105 ≤ (q.1 : ℂ).im ^ 2) :
    104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 105 ≤ v := by simpa only [v] using hhigh
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 104 * B ^ 2 < 104 * v := by rw [hB]; nlinarith
  have hprod : 0 ≤ (v - 105) * (v + 211 / 2 - 209 / 2) :=
    mul_nonneg (sub_nonneg.mpr hv) (by nlinarith)
  have hbase : 104 * v < (v - 1 / 4) ^ 2 := by nlinarith
  have hA0 : 0 < A := by dsimp only [A]; nlinarith
  have hleft : 0 < v - 1 / 4 := by nlinarith
  have hlt : v - 1 / 4 < A := by dsimp only [A]; nlinarith
  have hAsq : (v - 1 / 4) ^ 2 < A ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hleft hA0)]
  change 104 * B ^ 2 < A ^ 2
  linarith

theorem xiCenteredOrderSixteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 105 := by
  have hedge : (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    linarith [xiCenteredOrderSixteenSectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 105 := by
    by_contra h
    linarith [xiCenteredOrderSixteenSectorRatio_of_oneHundredFive_le_im_sq
      q (le_of_not_gt h)]
  exact ⟨hedge, hu, hvlow, hvhigh⟩

/-- Every centered reciprocal-square Xi atom has positive sixteenth-power real part. -/
theorem xiZeroCopyReciprocalSquare_pow_sixteen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 16).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  change 0 < ((((A : ℂ) - B * I)⁻¹) ^ 16).re
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
    apply orderSixteenReciprocalPower_re_pos_of_sectorRatio hA
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
    have hfail : A ^ 2 ≤ 104 * B ^ 2 := by
      by_contra h
      have hpos :=
        orderSixteenReciprocalPower_re_pos_of_sectorRatio hA (lt_of_not_ge h)
      have hnonpos : ((((A : ℂ) - B * I)⁻¹) ^ 16).re ≤ 0 :=
        le_of_not_gt hnot
      linarith
    have hc := xiCenteredOrderSixteenSectorFailure_mem_edgeCorner q hoff
      (by simpa only [A, B] using hfail)
    exact not_exists_xiZeroCopy_mem_centeredOrderSeventeen_sourceCorner
      ⟨q, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.trans (by norm_num)⟩

/-! ### Centered order seventeen -/

theorem xiCenteredOrderSeventeenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 6 : ℝ)) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 1 / 6 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hA : 509 / 6 < A := by dsimp only [A]; nlinarith
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 118 * B ^ 2 ≤ (236 / 3 : ℝ) * v := by rw [hB]; nlinarith
  have hfactor : 0 < A + 509 / 6 - 236 / 3 := by nlinarith
  have hprod : 0 < (A - 509 / 6) * (A + 509 / 6 - 236 / 3) :=
    mul_pos (sub_pos.mpr hA) hfactor
  have hpoly : (236 / 3 : ℝ) * (A + 1 / 6) < A ^ 2 := by nlinarith
  have hvA : v ≤ A + 1 / 6 := by dsimp only [A]; nlinarith
  change 118 * B ^ 2 < A ^ 2
  nlinarith

theorem xiCenteredOrderSeventeenSectorRatio_of_oneHundredNineteen_le_im_sq
    (q : XiZeroCopy) (hhigh : 119 ≤ (q.1 : ℂ).im ^ 2) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 119 ≤ v := by simpa only [v] using hhigh
  have hB : B ^ 2 = 4 * u * v := by dsimp only [B, u, v]; ring
  have hBbound : 118 * B ^ 2 < 118 * v := by rw [hB]; nlinarith
  have hprod : 0 ≤ (v - 119) * (v + 119 - 237 / 2) :=
    mul_nonneg (sub_nonneg.mpr hv) (by nlinarith)
  have hbase : 118 * v < (v - 1 / 4) ^ 2 := by nlinarith
  have hA0 : 0 < A := by dsimp only [A]; nlinarith
  have hleft : 0 < v - 1 / 4 := by nlinarith
  have hlt : v - 1 / 4 < A := by dsimp only [A]; nlinarith
  have hAsq : (v - 1 / 4) ^ 2 < A ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hleft hA0)]
  change 118 * B ^ 2 < A ^ 2
  linarith

theorem xiCenteredOrderSeventeenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 119 := by
  have hedge : (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    linarith [xiCenteredOrderSeventeenSectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 119 := by
    by_contra h
    linarith [xiCenteredOrderSeventeenSectorRatio_of_oneHundredNineteen_le_im_sq
      q (le_of_not_gt h)]
  exact ⟨hedge, hu, hvlow, hvhigh⟩

/-- Every centered reciprocal-square Xi atom has positive seventeenth-power real part. -/
theorem xiZeroCopyReciprocalSquare_pow_seventeen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 17).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  change 0 < ((((A : ℂ) - B * I)⁻¹) ^ 17).re
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
    apply orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA
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
    have hfail : A ^ 2 ≤ 118 * B ^ 2 := by
      by_contra h
      have hpos :=
        orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA (lt_of_not_ge h)
      have hnonpos : ((((A : ℂ) - B * I)⁻¹) ^ 17).re ≤ 0 :=
        le_of_not_gt hnot
      linarith
    have hc := xiCenteredOrderSeventeenSectorFailure_mem_edgeCorner q hoff
      (by simpa only [A, B] using hfail)
    exact not_exists_xiZeroCopy_mem_centeredOrderSeventeen_sourceCorner ⟨q, hc⟩

/-- Atomwise positivity of one centered reciprocal-square power implies positivity of the
corresponding normalized prime--archimedean moment. -/
theorem normalizedPrimeArchMoment_pos_of_atomwise_re_pos
    (n : ℕ)
    (hatom : ∀ q : XiZeroCopy,
      0 < (xiZeroCopyReciprocalSquare q ^ (n + 1)).re) :
    0 < normalizedPrimeArchMoment n := by
  classical
  have hmoment :
      (xiCentralReciprocalMoment n).re = normalizedPrimeArchMoment n := by
    have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment n
    simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
      congrArg Complex.re hsource.symm
  cases isEmpty_or_nonempty XiZeroCopy with
  | inl hEmpty =>
      letI : IsEmpty XiZeroCopy := hEmpty
      have hzero : xiCentralReciprocalMoment 0 = 0 := by
        rw [← tsum_xiZeroCopyReciprocalSquare_pow]
        simp
      have hzeroMoment :
          (xiCentralReciprocalMoment 0).re = normalizedPrimeArchMoment 0 := by
        have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 0
        simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
          congrArg Complex.re hsource.symm
      rw [hzero, Complex.zero_re] at hzeroMoment
      linarith [normalizedPrimeArchMoment_zero_pos]
  | inr hNonempty =>
      letI : Nonempty XiZeroCopy := hNonempty
      let q₀ : XiZeroCopy := Classical.choice hNonempty
      have hpow := summable_xiZeroCopyReciprocalSquare_pow n
      have hreal :
          Summable (fun q : XiZeroCopy =>
            (xiZeroCopyReciprocalSquare q ^ (n + 1)).re) :=
        Complex.reCLM.summable hpow
      have hsum :
          0 < ∑' q : XiZeroCopy,
            (xiZeroCopyReciprocalSquare q ^ (n + 1)).re :=
        hreal.tsum_pos (fun q => (hatom q).le) q₀ (hatom q₀)
      rw [← hmoment, ← tsum_xiZeroCopyReciprocalSquare_pow,
        Complex.re_tsum hpow]
      exact hsum

/-- The fifteenth normalized prime--archimedean source moment is strictly positive. -/
theorem normalizedPrimeArchMoment_fifteen_pos :
    0 < normalizedPrimeArchMoment 15 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 15
  simpa using xiZeroCopyReciprocalSquare_pow_sixteen_re_pos

/-- The sixteenth normalized prime--archimedean source moment is strictly positive. -/
theorem normalizedPrimeArchMoment_sixteen_pos :
    0 < normalizedPrimeArchMoment 16 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 16
  simpa using xiZeroCopyReciprocalSquare_pow_seventeen_re_pos

end

end RHTower
