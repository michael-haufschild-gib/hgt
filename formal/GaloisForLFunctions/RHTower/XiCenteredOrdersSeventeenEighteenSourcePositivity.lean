import GaloisForLFunctions.RHTower.XiCenteredOrdersFifteenSixteenSourcePositivity
import GaloisForLFunctions.RHTower.XiOrderEighteenEdgeCorner

/-!
# Centered orders seventeen and eighteen source positivity

The complete-source fourth-trace budget first forces every Xi zero below squared ordinate
`295/2` onto the critical line. In particular, centered order-eighteen sector failure lies in

`4/25 < (Re rho - 1/2)^(2 : ℕ) < 1/4`, `85 < (Im rho)^(2 : ℕ) < 133`,

and centered order-nineteen failure lies in

`7/50 < (Re rho - 1/2)^(2 : ℕ) < 1/4`, `85 < (Im rho)^(2 : ℕ) < 295/2`.

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
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < 295 / 2) :
    (9 / 200000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re :=
  nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_below_2365_over_16 q
    huLower huUpper hvLower (by linarith)

theorem not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner :
    ¬ ∃ q : XiZeroCopy,
      (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 295 / 2 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 :=
    re_ne_half_of_pos_centered_sq (by linarith)
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
        (q.1 : ℂ).im ^ (2 : ℕ) < 295 / 2 := by
  rintro ⟨q, hoff, hvUpper⟩
  have huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  have huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < (1 / 4 : ℝ) :=
    xi_divisor_support_centered_re_sq_lt_quarter q.1
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
    (hheight : (q.1 : ℂ).im ^ (2 : ℕ) < 295 / 2) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  exact not_exists_xiZeroCopy_offLine_of_im_sq_lt_twoHundredNinetyFiveHalves
    ⟨q, hoff, hheight⟩

theorem xiCenteredOrderEighteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (4 / 25 : ℝ)) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 132) (u₀ := 4 / 25)
      (v₀ := 85) (y₀ := 0) (y := 0) (by norm_num) le_rfl hinner
      (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

theorem xiCenteredOrderEighteenSectorRatio_of_oneHundredThirtyThree_le_im_sq
    (q : XiZeroCopy) (hhigh : 133 ≤ (q.1 : ℂ).im ^ (2 : ℕ)) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 132) (u₀ := 1 / 4)
      (v₀ := 133) (y₀ := 0) (y := 0) (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh (by norm_num) (by norm_num)

theorem xiCenteredOrderEighteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 133 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiCenteredOrderEighteenSectorRatio_of_offLine_inner q hoff h)
    (fun h => xiCenteredOrderEighteenSectorRatio_of_oneHundredThirtyThree_le_im_sq q h) hfail

theorem xiZeroCopyReciprocalSquare_pow_eighteen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ (18 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderEighteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderEighteenSectorFailure_mem_edgeCorner q hoff hfail)
    (fun hc => not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner
      ⟨q, by linarith [hc.1], hc.2.1, hc.2.2.1, hc.2.2.2.trans (by norm_num)⟩)

theorem xiCenteredOrderNineteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (7 / 50 : ℝ)) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 147) (u₀ := 7 / 50)
      (v₀ := 85) (y₀ := 0) (y := 0) (by norm_num) le_rfl hinner
      (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

theorem xiCenteredOrderNineteenSectorRatio_of_twoHundredNinetyFiveHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 295 / 2 ≤ (q.1 : ℂ).im ^ (2 : ℕ)) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 147) (u₀ := 1 / 4)
      (v₀ := 295 / 2) (y₀ := 0) (y := 0) (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh (by norm_num) (by norm_num)

theorem xiCenteredOrderNineteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 295 / 2 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiCenteredOrderNineteenSectorRatio_of_offLine_inner q hoff h)
    (fun h => xiCenteredOrderNineteenSectorRatio_of_twoHundredNinetyFiveHalves_le_im_sq q h) hfail

theorem xiZeroCopyReciprocalSquare_pow_nineteen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ (19 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderNineteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderNineteenSectorFailure_mem_edgeCorner q hoff hfail)
    (fun hc => not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner ⟨q, hc⟩)

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
