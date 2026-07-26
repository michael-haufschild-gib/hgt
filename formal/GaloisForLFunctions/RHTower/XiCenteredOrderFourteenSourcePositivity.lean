import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion

/-!
# Centered order-fourteen source positivity

The shifted order-fifteen source is positive for shifts above one quarter.  At the centered
coordinate, failure of the same rational sector condition can only occur in the compact corner

`1/6 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 101`.

Every zero in that corner contributes more than `1/20000` to the nonnegative fourth reciprocal
trace.  Its four distinct FE--Schwarz copies would therefore force the complete fourth trace
above `1/5000`, contradicting the existing source bound `9/50000`.

Thus every centered reciprocal-square Xi atom has positive fifteenth-power real part.  Absolute
summation proves the previously unresolved source sign
`normalizedPrimeArchMoment 14 > 0`, without a zero table or RH premise.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- In the inner centered strip, the height gap gives the order-fifteen sector condition. -/
theorem xiCenteredOrderFifteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 6 : ℝ)) :
    100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 1 / 6 := by simpa only [u] using hinner
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hA : 509 / 6 < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 100 * B ^ 2 ≤ (200 / 3 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hfactor : 0 < A + 509 / 6 - 200 / 3 := by nlinarith
  have hprod : 0 < (A - 509 / 6) * (A + 509 / 6 - 200 / 3) :=
    mul_pos (sub_pos.mpr hA) hfactor
  have hpoly : (200 / 3 : ℝ) * (A + 1 / 6) < A ^ 2 := by
    nlinarith
  have hvA : v ≤ A + 1 / 6 := by
    dsimp only [A]
    nlinarith
  change 100 * B ^ 2 < A ^ 2
  nlinarith

/-- Above squared height `101`, the full centered critical strip satisfies the order-fifteen
sector condition. -/
theorem xiCenteredOrderFifteenSectorRatio_of_oneHundredOne_le_im_sq
    (q : XiZeroCopy) (hhigh : 101 ≤ (q.1 : ℂ).im ^ 2) :
    100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 101 ≤ v := by simpa only [v] using hhigh
  have hv0 : 0 < v := by linarith
  have hA0 : 0 < A := by dsimp only [A]; nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 100 * B ^ 2 < 100 * v := by
    rw [hB]
    nlinarith
  have hprod : 0 ≤ (v - 101) * (v + 1 / 2) :=
    mul_nonneg (sub_nonneg.mpr hv) (by nlinarith)
  have hbase : 100 * v < (v - 1 / 4) ^ 2 := by
    nlinarith
  have hAsq : (v - 1 / 4) ^ 2 < A ^ 2 := by
    have hleft : 0 < v - 1 / 4 := by nlinarith
    have hlt : v - 1 / 4 < A := by
      dsimp only [A]
      nlinarith
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hleft hA0)]
  change 100 * B ^ 2 < A ^ 2
  linarith

/-- A centered order-fifteen sector failure lies in one compact edge corner. -/
theorem xiCenteredOrderFifteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 101 := by
  have hedge : (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    have hsector := xiCenteredOrderFifteenSectorRatio_of_offLine_inner
      q hoff (le_of_not_gt h)
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 85 < (q.1 : ℂ).im ^ 2 :=
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 101 := by
    by_contra h
    have hsector := xiCenteredOrderFifteenSectorRatio_of_oneHundredOne_le_im_sq
      q (le_of_not_gt h)
    linarith
  exact ⟨hedge, hu, hvlow, hvhigh⟩

/-- Every atom in the centered compact corner spends more than `1/20000` of the complete fourth
reciprocal trace. -/
theorem one_over_twentyThousand_lt_xiFourthReciprocalTraceAtom_of_centered_edgeCorner
    (q : XiZeroCopy)
    (huLower : (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 101) :
    (1 / 20000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 405 / 4
  have hu0 : 0 < u := by
    exact (by norm_num : (0 : ℝ) < 1 / 6).trans
      (by simpa only [u] using huLower)
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 101 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hw4 : w ^ 4 < W ^ 4 :=
    pow_lt_pow_left₀ hwUpper hw0.le (by norm_num)
  have huv : u * v < 101 / 4 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right (by simpa only [u] using huUpper) hv0
      _ < (1 / 4 : ℝ) * 101 :=
        mul_lt_mul_of_pos_left (by simpa only [v] using hvUpper) (by norm_num)
      _ = 101 / 4 := by ring
  have hw2 : 85 ^ 2 < w ^ 2 := by
    exact pow_lt_pow_left₀ hwLower (by norm_num) (by norm_num)
  have hnum :
      7023 < v ^ 2 - 6 * u * v + u ^ 2 := by
    have hid : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hid]
    nlinarith
  have hbudget : W ^ 4 < 20000 * 7023 := by
    norm_num [W]
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

/-- Four FE--Schwarz copies of a centered-corner zero would force the complete fourth trace above
`1/5000`. -/
theorem one_over_fiveThousand_lt_source_of_centeredOrderFourteen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 101) :
    (1 / 5000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    intro h
    rw [h] at huLower
    norm_num at huLower
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
  have hatom :=
    one_over_twentyThousand_lt_xiFourthReciprocalTraceAtom_of_centered_edgeCorner
      q huLower huUpper hvLower hvUpper
  nlinarith

/-- The centered order-fourteen compact corner contains no Xi divisor point. -/
theorem not_exists_xiZeroCopy_mem_centeredOrderFourteen_edgeCorner :
    ¬ ∃ q : XiZeroCopy,
      (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 101 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hlower :=
    one_over_fiveThousand_lt_source_of_centeredOrderFourteen_edgeCorner
      q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  nlinarith

/-- A nonpositive centered fifteenth reciprocal-power atom would lie in the excluded corner. -/
theorem xiCenteredOrderFifteenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 15).re ≤ 0) :
    (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 101 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hA : 0 < A := by dsimp only [A]; nlinarith
  have hfail : A ^ 2 ≤ 100 * B ^ 2 := by
    by_contra h
    have hsector : 100 * B ^ 2 < A ^ 2 := lt_of_not_ge h
    have hpos := orderFifteenReciprocalPower_re_pos_of_sectorRatio hA hsector
    change ((((A : ℂ) - B * I)⁻¹) ^ 15).re ≤ 0 at hnonpos
    linarith
  apply xiCenteredOrderFifteenSectorFailure_mem_edgeCorner q hoff
  simpa only [A, B, u, v] using hfail

/-- The centered order-fifteen coordinate has positive real part at every Xi divisor point. -/
theorem xiCenteredOrderFifteenCoordinate_re_pos
    (q : XiZeroCopy) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 15).re := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
    apply orderFifteenReciprocalPower_re_pos_of_sectorRatio hA
    dsimp only [A, B]
    rw [hoff]
    norm_num
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  · by_contra hnot
    have hcorner :=
      xiCenteredOrderFifteenReciprocalPower_nonpos_mem_edgeCorner
        q hoff (le_of_not_gt hnot)
    exact not_exists_xiZeroCopy_mem_centeredOrderFourteen_edgeCorner ⟨q, hcorner⟩

/-- The centered reciprocal-square atom is the inverse of the real-coordinate quadratic form. -/
theorem xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare q =
      (((((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 : ℝ) : ℂ) -
        (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im : ℝ) * I)⁻¹) := by
  rw [xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare]
  calc
    -((q.1 : ℂ) - 1 / 2)⁻¹ ^ 2 =
        -(((q.1 : ℂ) - 1 / 2) ^ 2)⁻¹ := by rw [inv_pow]
    _ = (-((q.1 : ℂ) - 1 / 2) ^ 2)⁻¹ := by rw [neg_inv]
    _ = (((((q.1 : ℂ).im ^ 2 -
          ((q.1 : ℂ).re - 1 / 2) ^ 2 : ℝ) : ℂ) -
          (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im : ℝ) * I)⁻¹) := by
      congr 1
      apply Complex.ext
      · simp [pow_two, Complex.mul_re, Complex.mul_im]
      · simp [pow_two, Complex.mul_re, Complex.mul_im]
        ring

/-- Every centered reciprocal-square Xi atom has positive fifteenth-power real part. -/
theorem xiZeroCopyReciprocalSquare_pow_fifteen_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 15).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  exact xiCenteredOrderFifteenCoordinate_re_pos q

/-- The fourteenth normalized prime--archimedean source moment is strictly positive. -/
theorem normalizedPrimeArchMoment_fourteen_pos :
    0 < normalizedPrimeArchMoment 14 := by
  classical
  have hmoment (n : ℕ) :
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
      have hre := hmoment 0
      rw [hzero, Complex.zero_re] at hre
      linarith [normalizedPrimeArchMoment_zero_pos]
  | inr hNonempty =>
      let q₀ : XiZeroCopy := Classical.choice hNonempty
      have hpow := summable_xiZeroCopyReciprocalSquare_pow 14
      have hreal :
          Summable (fun q : XiZeroCopy =>
            (xiZeroCopyReciprocalSquare q ^ 15).re) :=
        Complex.reCLM.summable hpow
      have hsum :
          0 < ∑' q : XiZeroCopy,
            (xiZeroCopyReciprocalSquare q ^ 15).re :=
        hreal.tsum_pos
          (fun q => (xiZeroCopyReciprocalSquare_pow_fifteen_re_pos q).le)
          q₀ (xiZeroCopyReciprocalSquare_pow_fifteen_re_pos q₀)
      rw [← hmoment 14, ← tsum_xiZeroCopyReciprocalSquare_pow,
        Complex.re_tsum hpow]
      exact hsum

end

end RHTower
