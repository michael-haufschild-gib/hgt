import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicityFarRay

open Complex

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- Sharpened degree-dependent squared-radius threshold. -/
def xiSquaredSharpFarRayThreshold (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 / 9 + 1 / 4

/-- The shifted squared spectral point lies in a `3/(2(n+1))` tangent sector once the
sharpened far-ray threshold is reached. -/
theorem xiSpectralSq_add_abs_im_lt_sharpSector (n : ℕ) {X : ℝ}
    (hX : xiSquaredSharpFarRayThreshold n ≤ X) (q : XiZeroCopy) :
    |(xiSpectralPoint q ^ 2 + (X : ℂ)).im| <
      (3 / (2 * ((n : ℝ) + 1))) *
        (xiSpectralPoint q ^ 2 + (X : ℂ)).re := by
  have hgammaSq : 2 < (xiSpectralPoint q).re ^ 2 := by
    have h := xiZeroCopy_two_lt_im_sq q
    rwa [← xiSpectralPoint_re_eq] at h
  have hb : |(xiSpectralPoint q).im| < 1 / 2 :=
    abs_xiSpectralPoint_im_lt_half q
  let gamma := (xiSpectralPoint q).re
  let b := (xiSpectralPoint q).im
  let m : ℝ := (n : ℝ) + 1
  let t : ℝ := 3 / (2 * m)
  have hm : 0 < m := by dsimp [m]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hgammaAbs : 0 < |gamma| := by
    rw [abs_pos]
    intro hzero
    dsimp [gamma] at hzero
    rw [hzero] at hgammaSq
    norm_num at hgammaSq
  have hbSq : b ^ 2 < 1 / 4 := by
    have hb' : |b| < 1 / 2 := by simpa [b] using hb
    nlinarith [sq_abs b, abs_nonneg b]
  have him : (xiSpectralPoint q ^ 2 + (X : ℂ)).im = 2 * gamma * b := by
    rw [Complex.add_im, Complex.ofReal_im, sq, Complex.mul_im]
    simp only [add_zero]
    dsimp [gamma, b]
    ring
  have hre : (xiSpectralPoint q ^ 2 + (X : ℂ)).re = gamma ^ 2 - b ^ 2 + X := by
    rw [Complex.add_re, Complex.ofReal_re, sq, Complex.mul_re]
    dsimp [gamma, b]
    ring
  have hB : |2 * gamma * b| < |gamma| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg b]
  have hboost : gamma ^ 2 + m ^ 2 / 9 < gamma ^ 2 - b ^ 2 + X := by
    unfold xiSquaredSharpFarRayThreshold at hX
    dsimp [m]
    nlinarith
  have hAMGMraw : 2 * m * |gamma| ≤ 3 * (gamma ^ 2 + m ^ 2 / 9) := by
    nlinarith [sq_nonneg (|gamma| - m / 3), sq_abs gamma]
  have hAMGM : |gamma| ≤ t * (gamma ^ 2 + m ^ 2 / 9) := by
    dsimp [t]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 2 * m)]
    nlinarith
  rw [him, hre]
  calc
    |2 * gamma * b| < |gamma| := hB
    _ ≤ t * (gamma ^ 2 + m ^ 2 / 9) := hAMGM
    _ < t * (gamma ^ 2 - b ^ 2 + X) :=
      mul_lt_mul_of_pos_left hboost ht
    _ = (3 / (2 * ((n : ℝ) + 1))) * (gamma ^ 2 - b ^ 2 + X) := by
      rfl

/-- Every shifted resolvent atom has positive `(n+1)`-st power at the sharpened far-ray
threshold. -/
theorem xiResolventPoint_pow_re_pos_sharpFarRay (n : ℕ) {X : ℝ}
    (hX : xiSquaredSharpFarRayThreshold n ≤ X) (q : XiZeroCopy) :
    0 < ((xiResolventPoint X q) ^ (n + 1)).re := by
  let w := xiSpectralPoint q ^ 2 + (X : ℂ)
  let A := w.re
  let B := -w.im
  let m : ℝ := (n : ℝ) + 1
  let t : ℝ := 3 / (2 * m)
  have hm : 0 < m := by dsimp [m]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hX0 : 0 ≤ X := by
    have hthreshold : 0 < xiSquaredSharpFarRayThreshold n := by
      unfold xiSquaredSharpFarRayThreshold
      positivity
    linarith
  have hA : 0 < A := by
    dsimp [A, w]
    linarith [xiSpectralSq_re_pos q]
  have hsector : |B| < t * A := by
    dsimp [A, B, w, t, m]
    simpa [Complex.add_im, Complex.add_re] using
      xiSpectralSq_add_abs_im_lt_sharpSector n hX q
  have hrepr : w = (A : ℂ) - B * I := by
    apply Complex.ext
    · simp [A, B]
    · simp [A, B]
  have hangle : ((n + 1 : ℕ) : ℝ) * t ≤ Real.pi / 2 := by
    have hmt : m * t = 3 / 2 := by
      dsimp [t]
      field_simp [ne_of_gt hm]
    have hpi := Real.pi_gt_three
    rw [Nat.cast_add, Nat.cast_one]
    change m * t ≤ Real.pi / 2
    rw [hmt]
    linarith
  rw [xiResolventPoint]
  change 0 < ((w⁻¹) ^ (n + 1)).re
  rw [hrepr]
  exact GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos hA hsector hangle

/-- Sharpened unconditional positivity of every resolvent moment. -/
theorem xiResolventMoment_re_pos_sharpFarRay (n : ℕ) {X : ℝ}
    (hX : xiSquaredSharpFarRayThreshold n ≤ X) :
    0 < (xiResolventMoment n X).re := by
  have hX0 : 0 ≤ X := by
    have hthreshold : 0 < xiSquaredSharpFarRayThreshold n := by
      unfold xiSquaredSharpFarRayThreshold
      positivity
    linarith
  have hsum := summable_xiResolventPoint_pow hX0 n
  rw [xiResolventMoment, Complex.re_tsum hsum]
  have hre : Summable (fun q : XiZeroCopy =>
      (xiResolventPoint X q ^ (n + 1)).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  exact hre.tsum_pos
    (fun q => (xiResolventPoint_pow_re_pos_sharpFarRay n hX q).le) q0
    (xiResolventPoint_pow_re_pos_sharpFarRay n hX q0)

/-- Shifted-reciprocal moment form of the sharpened far-ray law. -/
theorem re_xiShiftedReciprocalMoment_pos_sharpFarRay {y : ℝ} {n : ℕ}
    (hy : xiSquaredSharpFarRayThreshold n ≤ y) :
    0 < (xiShiftedReciprocalMoment y n).re := by
  have hy0 : 0 ≤ y := by
    have hthreshold : 0 < xiSquaredSharpFarRayThreshold n := by
      unfold xiSquaredSharpFarRayThreshold
      positivity
    linarith
  rw [xiShiftedReciprocalMoment_eq_xiResolventMoment hy0]
  exact xiResolventMoment_re_pos_sharpFarRay n hy

/-- **Factor-nine contraction of the C1 complete-monotonicity wedge.**  The `n`-th alternating
derivative of the exact squared-Xi radial field is positive already at
`y >= (n+1)^2/9 + 1/4`, unconditionally. -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos_sharpFarRay
    {y : ℝ} {n : ℕ} (hy : xiSquaredSharpFarRayThreshold n ≤ y) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField y := by
  have hy0 : 0 < y := by
    have hthreshold : 0 < xiSquaredSharpFarRayThreshold n := by
      unfold xiSquaredSharpFarRayThreshold
      positivity
    linarith
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [iteratedDeriv_squaredXiRadialField n hy0,
    show (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
        (xiShiftedReciprocalMoment y n).re) =
      ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) / 2 * (xiShiftedReciprocalMoment y n).re) by ring,
    hsq, one_mul]
  exact mul_pos (by positivity) (re_xiShiftedReciprocalMoment_pos_sharpFarRay hy)

end

end RHTower
