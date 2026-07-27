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
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 100) (u₀ := 1 / 6)
      (v₀ := 85) (y₀ := 0) (y := 0) (by norm_num) le_rfl hinner
      (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

/-- Above squared height `101`, the full centered critical strip satisfies the order-fifteen
sector condition. -/
theorem xiCenteredOrderFifteenSectorRatio_of_oneHundredOne_le_im_sq
    (q : XiZeroCopy) (hhigh : 101 ≤ (q.1 : ℂ).im ^ 2) :
    100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 100) (u₀ := 1 / 4)
      (v₀ := 101) (y₀ := 0) (y := 0) (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh (by norm_num) (by norm_num)

/-- A centered order-fifteen sector failure lies in one compact edge corner. -/
theorem xiCenteredOrderFifteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 6 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 101 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiCenteredOrderFifteenSectorRatio_of_offLine_inner q hoff h)
    (fun h => xiCenteredOrderFifteenSectorRatio_of_oneHundredOne_le_im_sq q h) hfail

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
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
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
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 :=
    re_ne_half_of_pos_centered_sq (by linarith)
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ 2).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := four_mul_le_tsum_of_quartet_invariant
    xiFourthReciprocalTraceAtom_nonneg hsum
    xiFourthReciprocalTraceAtom_lineConj xiFourthReciprocalTraceAtom_conj q hoff
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
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

/-- **A nonpositive centered reciprocal power falls into the sector-failure window.**  Off the
critical line the centered radial coordinate `A = im² - (re - 1/2)²` is positive, because
`im² > 85` while `(re - 1/2)² < 1/4`.  A positivity criterion then makes a nonpositive real part of
`((A - B i)⁻¹) ^ n` refute the sector ratio `N B² < A²`, and whatever `hwindow` concludes from the
failure holds. -/
theorem xiZeroCopy_centeredReciprocalPower_nonpos_of_sector {n : ℕ} {N : ℝ} {W : Prop}
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hcrit : ∀ A B : ℝ, 0 < A → N * B ^ 2 < A ^ 2 →
      0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re)
    (hwindow :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        N * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 → W)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ n).re ≤ 0) :
    W := by
  have hA : 0 < (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hv := xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
    linarith
  exact hwindow
    (GaloisForLFunctions.HTGeometry.sq_le_of_re_inv_sub_mul_I_pow_nonpos
      (fun h => hcrit _ _ hA h) hnonpos)

/-- **Centered coordinate power positivity from an empty window.**  On the critical line the
transverse coordinate vanishes and `A = im²` is nonzero, so the sector ratio is trivial; off it a
nonpositive real part lands the zero in the window `W`, which is empty. -/
theorem xiZeroCopy_centeredCoordinate_re_pos_of_window_empty {n : ℕ} {N : ℝ} {W : Prop}
    (q : XiZeroCopy)
    (hcrit : ∀ A B : ℝ, 0 < A → N * B ^ 2 < A ^ 2 →
      0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re)
    (hcorner : (q.1 : ℂ).re ≠ 1 / 2 →
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        N * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 → W)
    (hempty : ¬ W) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re := by
  intro A B
  have him : 0 < (q.1 : ℂ).im ^ 2 :=
    sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hB : B = 0 := by
      show 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im = 0
      rw [hoff]
      ring
    have hA : 0 < A := by
      show 0 < (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
      rw [hoff]
      nlinarith
    exact hcrit A B hA (by rw [hB]; simpa using pow_pos hA 2)
  · by_contra hnot
    exact hempty
      (xiZeroCopy_centeredReciprocalPower_nonpos_of_sector q hoff hcrit
        (hcorner hoff) (not_lt.mp hnot))

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
      (q.1 : ℂ).im ^ 2 < 101 :=
  xiZeroCopy_centeredReciprocalPower_nonpos_of_sector q hoff
    (fun _ _ hA h => orderFifteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiCenteredOrderFifteenSectorFailure_mem_edgeCorner q hoff) hnonpos

/-- The centered order-fifteen coordinate has positive real part at every Xi divisor point. -/
theorem xiCenteredOrderFifteenCoordinate_re_pos
    (q : XiZeroCopy) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 15).re :=
  xiZeroCopy_centeredCoordinate_re_pos_of_window_empty q
    (fun _ _ hA h => orderFifteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderFifteenSectorFailure_mem_edgeCorner q hoff hfail)
    (fun hc => not_exists_xiZeroCopy_mem_centeredOrderFourteen_edgeCorner ⟨q, hc⟩)

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

/-- **Centered reciprocal-square power positivity from an empty window.**  The centered radial
coordinate `A = im² - (re - 1/2)²` is positive at every Xi zero: on the critical line it is `im²`,
which is nonzero, and off it `im² > 85` while `(re - 1/2)² < 1/4`.  A nonpositive `n`-th power real
part therefore refutes the sector ratio `N B² < A²` and places the zero in the window `W`, which is
empty. -/
theorem xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty {n : ℕ} {N : ℝ} {W : Prop}
    (q : XiZeroCopy)
    (hcrit : ∀ A B : ℝ, 0 < A → N * B ^ 2 < A ^ 2 →
      0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re)
    (hcorner : (q.1 : ℂ).re ≠ 1 / 2 →
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        N * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 → W)
    (hempty : ¬ W) :
    0 < (xiZeroCopyReciprocalSquare q ^ n).re := by
  rw [xiZeroCopyReciprocalSquare_eq_centeredOrderCoordinate]
  exact xiZeroCopy_centeredCoordinate_re_pos_of_window_empty q hcrit hcorner hempty

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
