import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

namespace RHTower

/-- A complex number in the Xi reciprocal-square sector retains more than one eighth of its
thirteenth absolute moment in the real direction.  The proof is exact algebra: it uses the full
thirteenth-power polynomial rather than the quadratic cosine estimate that stops at exponent
twelve. -/
theorem re_pow_thirteen_gt_one_eighth_norm_pow_of_sector
    {z : ℂ} (hre : 0 < z.re)
    (hsector : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2) :
    (1 / 8 : ℝ) * ‖z‖ ^ 13 < (z ^ 13).re := by
  let x : ℝ := z.re
  let y : ℝ := z.im
  let X : ℝ := x ^ 2
  let Y : ℝ := y ^ 2
  have hx : 0 < x := by simpa only [x] using hre
  have hX : 0 < X := by exact sq_pos_of_pos hx
  have hY : 0 ≤ Y := sq_nonneg y
  have hsector' : Y ≤ X / 84 := by
    dsimp only [X, Y, x, y]
    norm_num at hsector ⊢
    nlinarith
  have h715 : 0 ≤ 715 * X - 1716 * Y := by nlinarith
  have h1287 : 0 ≤ 1287 * X - 286 * Y := by nlinarith
  have hgroup₁ : 0 ≤ X ^ 3 * Y ^ 2 * (715 * X - 1716 * Y) :=
    mul_nonneg (mul_nonneg (pow_nonneg hX.le 3) (pow_nonneg hY 2)) h715
  have hgroup₂ : 0 ≤ X * Y ^ 4 * (1287 * X - 286 * Y) :=
    mul_nonneg (mul_nonneg hX.le (pow_nonneg hY 4)) h1287
  have hdiff : 0 ≤ X - 84 * Y := by nlinarith
  have hlinear : 0 ≤ (2929 / 588 : ℝ) * X - (347 / 7 : ℝ) * Y := by
    nlinarith
  have hquadraticProduct :
      0 ≤ (X - 84 * Y) *
        ((2929 / 588 : ℝ) * X - (347 / 7 : ℝ) * Y) :=
    mul_nonneg hdiff hlinear
  have hquadratic :
      X ^ 2 / 6 ≤ X ^ 2 - 78 * X * Y + 694 * Y ^ 2 := by
    nlinarith
  have hbase :
      X ^ 6 / 6 ≤ X ^ 4 * (X ^ 2 - 78 * X * Y + 694 * Y ^ 2) := by
    have := mul_le_mul_of_nonneg_left hquadratic (pow_nonneg hX.le 4)
    nlinarith
  have hpoly :
      X ^ 6 / 6 ≤
        X ^ 6 - 78 * X ^ 5 * Y + 715 * X ^ 4 * Y ^ 2 -
          1716 * X ^ 3 * Y ^ 3 + 1287 * X ^ 2 * Y ^ 4 -
          286 * X * Y ^ 5 + 13 * Y ^ 6 := by
    nlinarith [hgroup₁, hgroup₂,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) (pow_nonneg hY 6)]
  have htwoRe : (z ^ 2).re = x ^ 2 - y ^ 2 := by
    rw [show z ^ 2 = z * z by ring, Complex.mul_re]
    dsimp only [x, y]
    ring
  have htwoIm : (z ^ 2).im = 2 * x * y := by
    rw [show z ^ 2 = z * z by ring, Complex.mul_im]
    dsimp only [x, y]
    ring
  have hfourRe :
      (z ^ 4).re = x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4 := by
    rw [show z ^ 4 = z ^ 2 * z ^ 2 by ring, Complex.mul_re, htwoRe, htwoIm]
    ring
  have hfourIm :
      (z ^ 4).im = 4 * x ^ 3 * y - 4 * x * y ^ 3 := by
    rw [show z ^ 4 = z ^ 2 * z ^ 2 by ring, Complex.mul_im, htwoRe, htwoIm]
    ring
  have heightRe :
      (z ^ 8).re =
        x ^ 8 - 28 * x ^ 6 * y ^ 2 + 70 * x ^ 4 * y ^ 4 -
          28 * x ^ 2 * y ^ 6 + y ^ 8 := by
    rw [show z ^ 8 = z ^ 4 * z ^ 4 by ring, Complex.mul_re, hfourRe, hfourIm]
    ring
  have heightIm :
      (z ^ 8).im =
        8 * x ^ 7 * y - 56 * x ^ 5 * y ^ 3 + 56 * x ^ 3 * y ^ 5 -
          8 * x * y ^ 7 := by
    rw [show z ^ 8 = z ^ 4 * z ^ 4 by ring, Complex.mul_im, hfourRe, hfourIm]
    ring
  have hre13 :
      (z ^ 13).re = x *
        (X ^ 6 - 78 * X ^ 5 * Y + 715 * X ^ 4 * Y ^ 2 -
          1716 * X ^ 3 * Y ^ 3 + 1287 * X ^ 2 * Y ^ 4 -
          286 * X * Y ^ 5 + 13 * Y ^ 6) := by
    rw [show z ^ 13 = (z ^ 8 * z ^ 4) * z by ring, Complex.mul_re,
      Complex.mul_re, Complex.mul_im, heightRe, heightIm, hfourRe, hfourIm]
    dsimp only [x, y, X, Y]
    ring
  have hreLower : x ^ 13 / 6 ≤ (z ^ 13).re := by
    rw [hre13]
    have := mul_le_mul_of_nonneg_left hpoly hx.le
    dsimp only [X] at this
    nlinarith
  have hnorm : ‖z‖ ≤ (85 / 84 : ℝ) * x := by
    apply (sq_le_sq₀ (norm_nonneg z) (mul_nonneg (by norm_num) hx.le)).mp
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    dsimp only [x]
    nlinarith [hsector]
  have hnorm13 : ‖z‖ ^ 13 ≤ ((85 / 84 : ℝ) * x) ^ 13 :=
    pow_le_pow_left₀ (norm_nonneg z) hnorm 13
  have hratio : (85 / 84 : ℝ) ^ 13 < 4 / 3 := by norm_num
  have hx13 : 0 < x ^ 13 := pow_pos hx 13
  have hnorm13' : ‖z‖ ^ 13 < (4 / 3 : ℝ) * x ^ 13 := by
    calc
      ‖z‖ ^ 13 ≤ ((85 / 84 : ℝ) * x) ^ 13 := hnorm13
      _ = (85 / 84 : ℝ) ^ 13 * x ^ 13 := by rw [mul_pow]
      _ < (4 / 3 : ℝ) * x ^ 13 := mul_lt_mul_of_pos_right hratio hx13
  nlinarith

/-- Every reciprocal-square Xi atom retains more than one eighth of its thirteenth absolute
moment in the real direction. -/
theorem re_xiZeroCopyReciprocalSquare_pow_thirteen_gt_one_eighth_norm_pow
    (q : XiZeroCopy) :
    (1 / 8 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ ^ 13 <
      (xiZeroCopyReciprocalSquare q ^ 13).re := by
  apply re_pow_thirteen_gt_one_eighth_norm_pow_of_sector
  · simpa only [xiThermalNode] using xiThermalNode_pos q
  · simpa only [xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q

/-- Every reciprocal-square Xi atom lies strictly inside the rational endpoint disk of radius
`2/41`. -/
theorem norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne
    (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ < (2 / 41 : ℝ) := by
  have hheight := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hspec : (41 / 2 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by
    rw [norm_xiSpectralPoint, Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  have hspecpos : 0 < ‖xiSpectralPoint q‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow]
  have hinv := (inv_lt_inv₀ hspecpos (by norm_num : (0 : ℝ) < 41 / 2)).2 hspec
  norm_num at hinv ⊢
  exact hinv

/-- Absolute thirteenth mass of the reciprocal-square Xi divisor. -/
noncomputable def xiShiftThirteenAbsoluteMass : ℝ :=
  ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ^ 13

theorem summable_xiShiftThirteenAbsoluteMass :
    Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ ^ 13) := by
  simpa only [norm_pow] using (summable_xiZeroCopyReciprocalSquare_pow 12).norm

/-- The thirteenth shifted source moment dominates one eighth of its absolute mass. -/
theorem one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve :
    (1 / 8 : ℝ) * xiShiftThirteenAbsoluteMass ≤ normalizedPrimeArchMoment 12 := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow 12
  have hre : Summable
      (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q ^ 13).re) :=
    Complex.reCLM.summable hpow
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow, Complex.re_tsum hpow,
    xiShiftThirteenAbsoluteMass, ← tsum_mul_left]
  exact (summable_xiShiftThirteenAbsoluteMass.mul_left (1 / 8 : ℝ)).tsum_le_tsum
    (fun q => (re_xiZeroCopyReciprocalSquare_pow_thirteen_gt_one_eighth_norm_pow q).le)
    hre

/-- The absolute tail after the thirteenth moment contracts at the rational endpoint radius. -/
theorem xiShiftThirteenAbsoluteTail_le (n : ℕ) :
    (∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ^ (13 + n)) ≤
      (2 / 41 : ℝ) ^ n * xiShiftThirteenAbsoluteMass := by
  have hleft : Summable
      (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ ^ (13 + n)) := by
    have h := (summable_xiZeroCopyReciprocalSquare_pow (12 + n)).norm
    simpa only [norm_pow, show 12 + n + 1 = 13 + n by omega] using h
  rw [xiShiftThirteenAbsoluteMass, ← tsum_mul_left]
  exact hleft.tsum_le_tsum (fun q => by
    rw [pow_add]
    have hpow : ‖xiZeroCopyReciprocalSquare q‖ ^ n ≤ (2 / 41 : ℝ) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le n
    exact (mul_le_mul_of_nonneg_left hpow (pow_nonneg (norm_nonneg _) 13)).trans_eq
      (mul_comm _ _))
    (summable_xiShiftThirteenAbsoluteMass.mul_left ((2 / 41 : ℝ) ^ n))

/-- Every later shifted source moment is bounded by the same geometric thirteenth-mass
envelope. -/
theorem abs_normalizedPrimeArchMoment_twelve_add_le (n : ℕ) :
    |normalizedPrimeArchMoment (12 + n)| ≤
      (2 / 41 : ℝ) ^ n * xiShiftThirteenAbsoluteMass := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow (12 + n)
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow]
  calc
    |(∑' q : XiZeroCopy,
        xiZeroCopyReciprocalSquare q ^ (12 + n + 1)).re| ≤
        ‖∑' q : XiZeroCopy,
          xiZeroCopyReciprocalSquare q ^ (12 + n + 1)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q ^ (12 + n + 1)‖ :=
      norm_tsum_le_tsum_norm hpow.norm
    _ = ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ ^ (13 + n) := by
      apply tsum_congr
      intro q
      rw [norm_pow]
      congr 1
      omega
    _ ≤ (2 / 41 : ℝ) ^ n * xiShiftThirteenAbsoluteMass :=
      xiShiftThirteenAbsoluteTail_le n

end RHTower
