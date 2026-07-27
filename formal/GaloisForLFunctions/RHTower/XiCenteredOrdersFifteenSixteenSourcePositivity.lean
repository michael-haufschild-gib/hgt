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
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ 2).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := four_mul_le_tsum_of_quartet_invariant
    xiFourthReciprocalTraceAtom_nonneg hsum
    xiFourthReciprocalTraceAtom_lineConj xiFourthReciprocalTraceAtom_conj q hoff
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
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
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
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
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 :=
    re_ne_half_of_pos_centered_sq (by linarith)
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
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 104) (u₀ := 1 / 6)
      (v₀ := 85) (y₀ := 0) (y := 0) (by norm_num) le_rfl hinner
      (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

theorem xiCenteredOrderSixteenSectorRatio_of_oneHundredFive_le_im_sq
    (q : XiZeroCopy) (hhigh : 105 ≤ (q.1 : ℂ).im ^ 2) :
    104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 104) (u₀ := 1 / 4)
      (v₀ := 105) (y₀ := 0) (y := 0) (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh (by norm_num) (by norm_num)

theorem xiCenteredOrderSixteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 105 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiCenteredOrderSixteenSectorRatio_of_offLine_inner q hoff h)
    (fun h => xiCenteredOrderSixteenSectorRatio_of_oneHundredFive_le_im_sq q h) hfail

/-- Every centered reciprocal-square Xi atom has positive sixteenth-power real part. -/
theorem xiZeroCopyReciprocalSquare_pow_sixteen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 16).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderSixteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderSixteenSectorFailure_mem_edgeCorner q hoff hfail)
    (fun hc => not_exists_xiZeroCopy_mem_centeredOrderSeventeen_sourceCorner
      ⟨q, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.trans (by norm_num)⟩)

/-! ### Centered order seventeen -/

theorem xiCenteredOrderSeventeenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 6 : ℝ)) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 118) (u₀ := 1 / 6)
      (v₀ := 85) (y₀ := 0) (y := 0) (by norm_num) le_rfl hinner
      (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

theorem xiCenteredOrderSeventeenSectorRatio_of_oneHundredNineteen_le_im_sq
    (q : XiZeroCopy) (hhigh : 119 ≤ (q.1 : ℂ).im ^ 2) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 118) (u₀ := 1 / 4)
      (v₀ := 119) (y₀ := 0) (y := 0) (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh (by norm_num) (by norm_num)

theorem xiCenteredOrderSeventeenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 119 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiCenteredOrderSeventeenSectorRatio_of_offLine_inner q hoff h)
    (fun h => xiCenteredOrderSeventeenSectorRatio_of_oneHundredNineteen_le_im_sq q h) hfail

/-- Every centered reciprocal-square Xi atom has positive seventeenth-power real part. -/
theorem xiZeroCopyReciprocalSquare_pow_seventeen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 17).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderSeventeenSectorFailure_mem_edgeCorner q hoff hfail)
    (fun hc => not_exists_xiZeroCopy_mem_centeredOrderSeventeen_sourceCorner ⟨q, hc⟩)

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
