import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicitySharpFarRay

open Complex

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- Optimal threshold supplied by the uniform open-strip tangent-sector argument. -/
def xiSquaredPiFarRayThreshold (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (2 : ℕ) / Real.pi ^ (2 : ℕ) + 1 / 4

/-- Exact `pi/(2(n+1))` tangent sector at the optimal uniform-strip threshold. -/
theorem xiSpectralSq_add_abs_im_lt_piSector (n : ℕ) {X : ℝ}
    (hX : xiSquaredPiFarRayThreshold n ≤ X) (q : XiZeroCopy) :
    |(xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im| <
      (Real.pi / (2 * ((n : ℝ) + 1))) *
        (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re := by
  have hgammaSq : 2 < (xiSpectralPoint q).re ^ (2 : ℕ) := by
    have h := xiZeroCopy_two_lt_im_sq q
    rwa [← xiSpectralPoint_re_eq] at h
  have hb : |(xiSpectralPoint q).im| < 1 / 2 :=
    abs_xiSpectralPoint_im_lt_half q
  let gamma := (xiSpectralPoint q).re
  let b := (xiSpectralPoint q).im
  let m : ℝ := (n : ℝ) + 1
  let t : ℝ := Real.pi / (2 * m)
  have hm : 0 < m := by dsimp [m]; positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht : 0 < t := by dsimp [t]; positivity
  have hgammaAbs : 0 < |gamma| := by
    rw [abs_pos]
    intro hzero
    dsimp [gamma] at hzero
    rw [hzero] at hgammaSq
    norm_num at hgammaSq
  have hbSq : b ^ (2 : ℕ) < 1 / 4 := by
    have hb' : |b| < 1 / 2 := by simpa [b] using hb
    nlinarith [sq_abs b, abs_nonneg b]
  have him : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im = 2 * gamma * b := by
    rw [Complex.add_im, Complex.ofReal_im, sq, Complex.mul_im]
    simp only [add_zero]
    dsimp [gamma, b]
    ring
  have hre : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re = gamma ^ (2 : ℕ) - b ^ (2 : ℕ) + X := by
    rw [Complex.add_re, Complex.ofReal_re, sq, Complex.mul_re]
    dsimp [gamma, b]
    ring
  have hB : |2 * gamma * b| < |gamma| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg b]
  have hboost : gamma ^ (2 : ℕ) + m ^ (2 : ℕ) / Real.pi ^ (2 : ℕ) <
      gamma ^ (2 : ℕ) - b ^ (2 : ℕ) + X := by
    unfold xiSquaredPiFarRayThreshold at hX
    dsimp [m]
    nlinarith
  have hAMGMraw : 2 * m * |gamma| ≤
      Real.pi * (gamma ^ (2 : ℕ) + m ^ (2 : ℕ) / Real.pi ^ (2 : ℕ)) := by
    have hid : Real.pi * (gamma ^ (2 : ℕ) + m ^ (2 : ℕ) / Real.pi ^ (2 : ℕ)) -
        2 * m * |gamma| = Real.pi * (|gamma| - m / Real.pi) ^ (2 : ℕ) := by
      field_simp [Real.pi_ne_zero]
      nlinarith [sq_abs gamma]
    rw [← sub_nonneg, hid]
    positivity
  have hAMGM : |gamma| ≤ t *
      (gamma ^ (2 : ℕ) + m ^ (2 : ℕ) / Real.pi ^ (2 : ℕ)) := by
    dsimp [t]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 2 * m)]
    nlinarith
  rw [him, hre]
  calc
    |2 * gamma * b| < |gamma| := hB
    _ ≤ t * (gamma ^ (2 : ℕ) + m ^ (2 : ℕ) / Real.pi ^ (2 : ℕ)) := hAMGM
    _ < t * (gamma ^ (2 : ℕ) - b ^ (2 : ℕ) + X) :=
      mul_lt_mul_of_pos_left hboost ht
    _ = (Real.pi / (2 * ((n : ℝ) + 1))) *
        (gamma ^ (2 : ℕ) - b ^ (2 : ℕ) + X) := by rfl

theorem xiResolventPoint_pow_re_pos_piFarRay (n : ℕ) {X : ℝ}
    (hX : xiSquaredPiFarRayThreshold n ≤ X) (q : XiZeroCopy) :
    0 < ((xiResolventPoint X q) ^ (n + 1)).re := by
  let w := xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)
  let A := w.re
  let B := -w.im
  let m : ℝ := (n : ℝ) + 1
  let t : ℝ := Real.pi / (2 * m)
  have hm : 0 < m := by dsimp [m]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hX0 : 0 ≤ X := by
    have hthreshold : 0 < xiSquaredPiFarRayThreshold n := by
      unfold xiSquaredPiFarRayThreshold
      positivity
    linarith
  have hA : 0 < A := by
    dsimp [A, w]
    linarith [xiSpectralSq_re_pos q]
  have hsector : |B| < t * A := by
    dsimp [A, B, w, t, m]
    simpa [Complex.add_im, Complex.add_re] using
      xiSpectralSq_add_abs_im_lt_piSector n hX q
  have hrepr : w = (A : ℂ) - B * I := by
    apply Complex.ext
    · simp [A, B]
    · simp [A, B]
  have hangle : ((n + 1 : ℕ) : ℝ) * t ≤ Real.pi / 2 := by
    have hmt : m * t = Real.pi / 2 := by
      dsimp [t]
      field_simp [ne_of_gt hm]
    rw [Nat.cast_add, Nat.cast_one]
    change m * t ≤ Real.pi / 2
    rw [hmt]
  rw [xiResolventPoint]
  change 0 < ((w⁻¹) ^ (n + 1)).re
  rw [hrepr]
  exact GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos hA hsector hangle

theorem xiResolventMoment_re_pos_piFarRay (n : ℕ) {X : ℝ}
    (hX : xiSquaredPiFarRayThreshold n ≤ X) :
    0 < (xiResolventMoment n X).re := by
  have hX0 : 0 ≤ X := by
    have hthreshold : 0 < xiSquaredPiFarRayThreshold n := by
      unfold xiSquaredPiFarRayThreshold
      positivity
    linarith
  have hsum := summable_xiResolventPoint_pow hX0 n
  rw [xiResolventMoment, Complex.re_tsum hsum]
  have hre : Summable (fun q : XiZeroCopy =>
      (xiResolventPoint X q ^ (n + 1)).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  exact hre.tsum_pos
    (fun q => (xiResolventPoint_pow_re_pos_piFarRay n hX q).le) q0
    (xiResolventPoint_pow_re_pos_piFarRay n hX q0)

theorem re_xiShiftedReciprocalMoment_pos_piFarRay {y : ℝ} {n : ℕ}
    (hy : xiSquaredPiFarRayThreshold n ≤ y) :
    0 < (xiShiftedReciprocalMoment y n).re := by
  have hy0 : 0 ≤ y := by
    have hthreshold : 0 < xiSquaredPiFarRayThreshold n := by
      unfold xiSquaredPiFarRayThreshold
      positivity
    linarith
  rw [xiShiftedReciprocalMoment_eq_xiResolventMoment hy0]
  exact xiResolventMoment_re_pos_piFarRay n hy

/-- **Optimal uniform-sector contraction of the C1 wedge.**  Alternating derivative positivity
holds unconditionally at `y >= (n+1)^(2 : ℕ)/pi^(2 : ℕ) + 1/4`. -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos_piFarRay
    {y : ℝ} {n : ℕ} (hy : xiSquaredPiFarRayThreshold n ≤ y) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField y := by
  have hy0 : 0 < y := by
    have hthreshold : 0 < xiSquaredPiFarRayThreshold n := by
      unfold xiSquaredPiFarRayThreshold
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
  exact mul_pos (by positivity) (re_xiShiftedReciprocalMoment_pos_piFarRay hy)

end

end RHTower
