import GaloisForLFunctions.RHTower.XiGaussianQuadraticSplitting
import GaloisForLFunctions.RHTower.XiGaussianNativeHeatDissipation
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity

/-!
# A same-time, all-order bound on quadratic splitting's transverse loss

The actual open strip and source-derived height gap give
`339 * (im w)^2 < 340 * re w` at every squared spectral node.
The resulting transverse-energy bound keeps the entire cofactor polynomial.
It gives lower bounds for the actual native and real-channel energies after
quadratic splitting, without moving heat time or truncating polynomial order.
The first native moment is retained explicitly, not assumed bounded by mass.
-/

open Complex Polynomial
noncomputable section
namespace RHTower

def xiGaussianNativeFirstMoment (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  ∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2).re *
    ‖xiPolynomialGaussianHeatTerm P t q‖

/-- A parabolic spectral bound, obtained without numerical zero identification. -/
theorem xiSpectralSq_transverse_moment_bound (q : XiZeroCopy) :
    339 * (xiSpectralPoint q ^ 2).im ^ 2 < 340 * (xiSpectralPoint q ^ 2).re := by
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have hz : (xiSpectralPoint q).im = 0 := by simp [xiSpectralPoint, hon]
    have hw : (xiSpectralPoint q ^ 2).im = 0 := by simp [pow_two, Complex.mul_im, hz]
    simpa only [hw, zero_pow two_ne_zero, mul_zero] using
      mul_pos (show (0 : ℝ) < 340 by norm_num) (xiSpectralSq_re_pos q)
  have hheight : (85 : ℝ) < (q.1 : ℂ).im ^ 2 := by
    have h := xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq q hon
    linarith only [h]
  have hwidth := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
    simp [xiSpectralPoint]
  have hx : 0 < (q.1 : ℂ).im ^ 2 := lt_trans (by norm_num) hheight
  have hprod := mul_lt_mul_of_pos_left hwidth hx
  simp only [pow_two, Complex.mul_re, Complex.mul_im, hre, him]
  nlinarith only [hheight, hwidth, hprod]

private theorem first_atom_le (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy)
    (η : {η : ℝ // 0 < η}) :
    2 * ((xiSpectralPoint q ^ 2).re * ‖xiPolynomialGaussianHeatTerm P t q‖) ≤
      (η : ℝ) * ‖xiPolynomialGaussianHeatTerm (P * X) t q‖ +
        (η : ℝ)⁻¹ * ‖xiPolynomialGaussianHeatTerm P t q‖ := by
  have hre := Complex.re_le_norm (xiSpectralPoint q ^ 2)
  have hb : 2 * (xiSpectralPoint q ^ 2).re ≤
      (η : ℝ) * ‖xiSpectralPoint q ^ 2‖ ^ 2 + (η : ℝ)⁻¹ := by
    have he : (η : ℝ) * (η : ℝ)⁻¹ = 1 := mul_inv_cancel₀ η.property.ne'
    have hs := sq_nonneg ((η : ℝ) * ‖xiSpectralPoint q ^ 2‖ - 1)
    apply le_of_mul_le_mul_left (a := (η : ℝ)) ?_ η.property
    nlinarith only [hs, he, mul_le_mul_of_nonneg_left hre η.property.le]
  have h := mul_le_mul_of_nonneg_right hb (norm_nonneg (xiPolynomialGaussianHeatTerm P t q))
  rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm,
    evalRealPolynomial_mul, evalRealPolynomial_X, norm_mul, mul_pow]
  rw [norm_xiPolynomialGaussianHeatTerm] at h
  nlinarith only [h]

theorem summable_xiGaussianNativeFirstMoment (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    Summable (fun q : XiZeroCopy => (xiSpectralPoint q ^ 2).re *
      ‖xiPolynomialGaussianHeatTerm P t q‖) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (xiSpectralSq_re_pos q).le (norm_nonneg _)) _
    ((summable_norm_xiPolynomialGaussianHeatTerm t.property (P * X)).add
      (summable_norm_xiPolynomialGaussianHeatTerm t.property P))
  intro q
  have h := first_atom_le P t q ⟨1, one_pos⟩
  dsimp only at h
  simp only [one_mul, inv_one] at h
  nlinarith only [h, mul_nonneg (xiSpectralSq_re_pos q).le
    (norm_nonneg (xiPolynomialGaussianHeatTerm P t q))]

theorem xiGaussianNativeFirstMoment_nonneg (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) : 0 ≤ xiGaussianNativeFirstMoment P t :=
  tsum_nonneg fun q => mul_nonneg (xiSpectralSq_re_pos q).le (norm_nonneg _)

/-- One constant controls every coefficient vector, degree, and positive heat time. -/
theorem xiGaussianTransverseEnergy_le_firstMoment (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianTransverseEnergy P t ≤ (340 / 339 : ℝ) * xiGaussianNativeFirstMoment P t := by
  have hp (q : XiZeroCopy) :
      (xiSpectralPoint q ^ 2).im ^ 2 * ‖xiPolynomialGaussianHeatTerm P t q‖ ≤
        (340 / 339 : ℝ) * ((xiSpectralPoint q ^ 2).re * ‖xiPolynomialGaussianHeatTerm P t q‖) := by
    have hs := xiSpectralSq_transverse_moment_bound q
    have h := mul_le_mul_of_nonneg_right
      (show (xiSpectralPoint q ^ 2).im ^ 2 ≤ (340 / 339 : ℝ) * (xiSpectralPoint q ^ 2).re by
        linarith only [hs]) (norm_nonneg (xiPolynomialGaussianHeatTerm P t q))
    simpa only [mul_assoc] using h
  have h := Summable.tsum_le_tsum hp
    (summable_xiGaussianTransverseEnergy P t)
    ((summable_xiGaussianNativeFirstMoment P t).mul_left (340 / 339 : ℝ))
  rw [tsum_mul_left] at h
  exact h

/-- A tunable bound involving only native energies at the same time. -/
theorem xiGaussianNativeFirstMoment_young_bound (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (η : {η : ℝ // 0 < η}) :
    2 * xiGaussianNativeFirstMoment P t ≤
      (η : ℝ) * xiGaussianNativeEnergy (P * X) t +
        (η : ℝ)⁻¹ * xiGaussianNativeEnergy P t := by
  have h := Summable.tsum_le_tsum (first_atom_le P t · η)
    ((summable_xiGaussianNativeFirstMoment P t).mul_left 2)
    (((summable_norm_xiPolynomialGaussianHeatTerm t.property (P * X)).mul_left (η : ℝ)).add
      ((summable_norm_xiPolynomialGaussianHeatTerm t.property P).mul_left (η : ℝ)⁻¹))
  rw [tsum_mul_left, Summable.tsum_add
    ((summable_norm_xiPolynomialGaussianHeatTerm t.property (P * X)).mul_left (η : ℝ))
    ((summable_norm_xiPolynomialGaussianHeatTerm t.property P).mul_left (η : ℝ)⁻¹),
    tsum_mul_left, tsum_mul_left] at h
  exact h

/-- A genuine lower bound on the full native energy after a quadratic factor. -/
theorem xiGaussianNativeEnergy_quadratic_lower (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianNativeEnergy (P * xiGaussianLinearFactor a ^ 2) t +
      2 * b ^ 2 * xiGaussianNativeEnergy (P * xiGaussianLinearFactor a) t +
      b ^ 4 * xiGaussianNativeEnergy P t -
      (1360 / 339 : ℝ) * b ^ 2 * xiGaussianNativeFirstMoment P t ≤
        xiGaussianNativeEnergy (P * xiGaussianPositiveQuadratic a b) t := by
  have he := xiGaussianNativeEnergy_quadratic_split P a b t
  have hb := mul_le_mul_of_nonneg_left (xiGaussianTransverseEnergy_le_firstMoment P t)
    (show 0 ≤ 4 * b ^ 2 by positivity)
  nlinarith only [he, hb]

/-- Positive real-channel energies retain their complete same-time correction. -/
theorem xiGaussianRealChannel_quadratic_lower (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy (P * xiGaussianLinearFactor a ^ 2) t +
      2 * b ^ 2 * xiGaussianRealChannelEnergy (P * xiGaussianLinearFactor a) t +
      b ^ 4 * xiGaussianRealChannelEnergy P t -
      (680 / 339 : ℝ) * b ^ 2 * xiGaussianNativeFirstMoment P t ≤
        xiGaussianRealChannelEnergy (P * xiGaussianPositiveQuadratic a b) t := by
  have he := xiGaussianRealChannel_quadratic_split P a b t
  have hb := mul_le_mul_of_nonneg_left (xiGaussianTransverseEnergy_le_firstMoment P t)
    (show 0 ≤ 2 * b ^ 2 by positivity)
  nlinarith only [he, hb]

/-- The quartet height also gives a small coefficient against the next native energy. -/
theorem xiSpectralSq_transverse_secondMoment_bound (q : XiZeroCopy) :
    84 * (xiSpectralPoint q ^ 2).im ^ 2 < ‖xiSpectralPoint q ^ 2‖ ^ 2 := by
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have hz : (xiSpectralPoint q).im = 0 := by simp [xiSpectralPoint, hon]
    have hw : (xiSpectralPoint q ^ 2).im = 0 := by simp [pow_two, Complex.mul_im, hz]
    have hn : 0 < ‖xiSpectralPoint q ^ 2‖ :=
      (xiSpectralSq_re_pos q).trans_le (Complex.re_le_norm _)
    simpa only [hw, zero_pow two_ne_zero, mul_zero] using sq_pos_of_pos hn
  have hheight :=
    xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq q hon
  have hwidth := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hx : 0 < (q.1 : ℂ).im ^ 2 := by linarith only [hheight]
  have hprod := mul_lt_mul_of_pos_left hwidth hx
  have hxp := mul_lt_mul_of_pos_left
    (show (84 : ℝ) < (q.1 : ℂ).im ^ 2 by linarith only [hheight]) hx
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
    simp [xiSpectralPoint]
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_im, hre, him]
  nlinarith only [hprod, hxp, sq_nonneg (((q.1 : ℂ).re - 1/2) ^ 2),
    mul_nonneg (sq_nonneg (q.1 : ℂ).im) (sq_nonneg ((q.1 : ℂ).re - 1/2))]

/-- The full transverse cost is at most one eighty-fourth of the next native energy. -/
theorem xiGaussianTransverseEnergy_le_nextEnergy (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianTransverseEnergy P t ≤ (1 / 84 : ℝ) * xiGaussianNativeEnergy (P * X) t := by
  have hp (q : XiZeroCopy) :
      (xiSpectralPoint q ^ 2).im ^ 2 * ‖xiPolynomialGaussianHeatTerm P t q‖ ≤
        (1 / 84 : ℝ) * ‖xiPolynomialGaussianHeatTerm (P * X) t q‖ := by
    have hs := xiSpectralSq_transverse_secondMoment_bound q
    have h := mul_le_mul_of_nonneg_right
      (show (xiSpectralPoint q ^ 2).im ^ 2 ≤ (1 / 84 : ℝ) * ‖xiSpectralPoint q ^ 2‖ ^ 2 by
        linarith only [hs]) (norm_nonneg (xiPolynomialGaussianHeatTerm P t q))
    rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm,
      evalRealPolynomial_mul, evalRealPolynomial_X, norm_mul, mul_pow]
    rw [norm_xiPolynomialGaussianHeatTerm] at h
    nlinarith only [h]
  have h := Summable.tsum_le_tsum hp (summable_xiGaussianTransverseEnergy P t)
    ((summable_norm_xiPolynomialGaussianHeatTerm t.property (P * X)).mul_left (1 / 84 : ℝ))
  rw [tsum_mul_left] at h
  exact h

/-- Same-time native lower bound with a fixed, degree-independent correction coefficient. -/
theorem xiGaussianNativeEnergy_quadratic_nextEnergy_lower (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianNativeEnergy (P * xiGaussianLinearFactor a ^ 2) t +
      2 * b ^ 2 * xiGaussianNativeEnergy (P * xiGaussianLinearFactor a) t +
      b ^ 4 * xiGaussianNativeEnergy P t -
      (1 / 21 : ℝ) * b ^ 2 * xiGaussianNativeEnergy (P * X) t ≤
        xiGaussianNativeEnergy (P * xiGaussianPositiveQuadratic a b) t := by
  have he := xiGaussianNativeEnergy_quadratic_split P a b t
  have hb := mul_le_mul_of_nonneg_left (xiGaussianTransverseEnergy_le_nextEnergy P t)
    (show 0 ≤ 4 * b ^ 2 by positivity)
  nlinarith only [he, hb]

/-- The corresponding retained real-channel bound has half the native correction. -/
theorem xiGaussianRealChannel_quadratic_nextEnergy_lower (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy (P * xiGaussianLinearFactor a ^ 2) t +
      2 * b ^ 2 * xiGaussianRealChannelEnergy (P * xiGaussianLinearFactor a) t +
      b ^ 4 * xiGaussianRealChannelEnergy P t -
      (1 / 42 : ℝ) * b ^ 2 * xiGaussianNativeEnergy (P * X) t ≤
        xiGaussianRealChannelEnergy (P * xiGaussianPositiveQuadratic a b) t := by
  have he := xiGaussianRealChannel_quadratic_split P a b t
  have hb := mul_le_mul_of_nonneg_left (xiGaussianTransverseEnergy_le_nextEnergy P t)
    (show 0 ≤ 2 * b ^ 2 by positivity)
  nlinarith only [he, hb]

end RHTower
