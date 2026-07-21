import GaloisForLFunctions.RHTower.HedenmalmGaussianHankelRH
import GaloisForLFunctions.RHTower.PrimeArchHighFrequencyAccretivity
import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility

/-!
# Unconditional exterior positivity of the complete Hedenmalm Gaussian Hankel tower

Every centered Xi zero lies in the open band `|Im z| < 1/2`.  Consequently, on the lower
exterior half-plane `Im z ≤ -1/2`, each relative-resolvent atom paired with its critical-line
conjugate has nonnegative imaginary part.  Summation gives the global exterior orientation sign
with no frequency cutoff.  The exact Fourier-current identity and the complete weighted-moment
cone theorem then prove positivity of the entire Gaussian Hankel tower at every exterior aperture
`1/2 ≤ a < 1` and every positive temperature.

This is the sharp unconditional exterior phase of the Hedenmalm criterion.  The corresponding
interior family `0 < a < 1/2` remains equivalent to the Riemann hypothesis.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- On the lower exterior half-plane, every conjugate-paired Xi relative-resolvent atom has
nonnegative imaginary part. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonneg_lowerExterior
    (z : ℂ) (hzIm : z.im ≤ -(1 / 2)) (q : XiZeroCopy) :
    0 ≤ (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im := by
  let a : ℂ := xiSpectralPoint q
  have haimMem := xiSpectralPoint_im_mem_openHalf q
  have haimSq : a.im ^ 2 < z.im ^ 2 := by
    nlinarith [sq_nonneg (a.im + 1 / 2), sq_nonneg (1 / 2 - a.im),
      sq_nonneg (z.im + 1 / 2)]
  have hcore : 0 < (z.re - a.re) ^ 2 + z.im ^ 2 - a.im ^ 2 := by
    nlinarith [sq_nonneg (z.re - a.re)]
  have hza : z ≠ a := by
    intro h
    have him := congrArg Complex.im h
    linarith [haimMem.1]
  have hzac : z ≠ (starRingEnd ℂ) a := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.conj_im] at him
    linarith [haimMem.2]
  have hdenOne :
      0 < (z.re - a.re) ^ 2 + (z.im - a.im) ^ 2 := by
    have h : z - a ≠ 0 := sub_ne_zero.mpr hza
    simpa only [Complex.normSq_apply, sub_re, sub_im, pow_two] using
      Complex.normSq_pos.mpr h
  have hdenTwo :
      0 < (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 := by
    have h : z - (starRingEnd ℂ) a ≠ 0 := sub_ne_zero.mpr hzac
    simpa only [Complex.normSq_apply, Complex.conj_re, Complex.conj_im,
      sub_re, sub_im, sub_neg_eq_add, pow_two] using Complex.normSq_pos.mpr h
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
    xiSpectralPoint_lineConj]
  change 0 ≤ ((a⁻¹ - (a - z)⁻¹) +
      (((starRingEnd ℂ) a)⁻¹ - ((starRingEnd ℂ) a - z)⁻¹)).im
  rw [relativeResolvent_conj_pair_im_formula z a
    (xiSpectralPoint_ne_zero q) hza (by simpa using hzac)]
  exact div_nonneg
    (mul_nonneg (by nlinarith [hzIm]) hcore.le)
    (mul_nonneg hdenOne.le hdenTwo.le)

/-- The full Xi relative-resolvent trace has nonnegative imaginary part throughout the lower
exterior half-plane. -/
theorem xiRelativeResolventTrace_im_nonneg_lowerExterior
    (z : ℂ) (hzIm : z.im ≤ -(1 / 2)) :
    0 ≤ (xiRelativeResolventTrace z).im := by
  have hzAbs : 1 / 2 ≤ |z.im| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hXi : XiC z ≠ 0 :=
    SlabFullWidthAdmissibility.XiC_ne_zero_of_half_le_abs_im hzAbs
  have hsum := summable_xiRelativeResolventTerm hXi
  have hsumJ : Summable (fun q : XiZeroCopy =>
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpair := hsum.add hsumJ
  have hreindex :
      (∑' q : XiZeroCopy,
        xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)) =
          xiRelativeResolventTrace z := by
    rw [xiRelativeResolventTrace]
    exact xiZeroCopyLineConjEquiv.tsum_eq (xiRelativeResolventTerm z)
  have hpairsum :
      (∑' q : XiZeroCopy,
        (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q))) =
        2 * xiRelativeResolventTrace z := by
    rw [hsum.tsum_add hsumJ, hreindex, xiRelativeResolventTrace]
    ring
  have himsum :
      0 ≤ (∑' q : XiZeroCopy,
        (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im) :=
    tsum_nonneg fun q =>
      xiRelativeResolventTerm_lineConj_pair_im_nonneg_lowerExterior z hzIm q
  have hpairsumIm := congrArg Complex.im hpairsum
  rw [Complex.im_tsum hpair] at hpairsumIm
  norm_num [mul_im] at hpairsumIm
  have himsum' :
      0 ≤ (∑' q : XiZeroCopy,
        ((xiRelativeResolventTerm z q).im +
          (xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im)) := by
    simpa only [add_im] using himsum
  linarith

/-- Algebraic conversion of the split current into logarithmic-derivative orientation. -/
lemma kreinCurrent_eq_normSq_mul_logDeriv_im
    (u v : ℂ) (hu : u ≠ 0) :
    2 * (((starRingEnd ℂ) u) * (-I * v)).re =
      2 * Complex.normSq u * (v / u).im := by
  rw [Complex.div_im]
  simp only [mul_re, mul_im, conj_re, conj_im, neg_re, neg_im, I_re, I_im,
    Complex.normSq_apply]
  have hnorm : u.re ^ 2 + u.im ^ 2 ≠ 0 := by
    simpa only [Complex.normSq_apply, pow_two] using
      (Complex.normSq_pos.mpr hu).ne'
  field_simp [hnorm]
  ring

/-- The actual theta/Xi orbit lies in the nonnegative Krein chamber at every exterior aperture,
globally in frequency. -/
theorem thetaXiHankelOrbit_kreinForm_nonneg_of_half_le
    {a : ℝ} (ha : 1 / 2 ≤ a) (b : ℝ) :
    0 ≤ hedenmalmHankelKreinForm
      (thetaXiHankelOrbitValuePlus a b)
      (thetaXiHankelOrbitTangentPlus a b)
      (thetaXiHankelOrbitValueMinus a b)
      (thetaXiHankelOrbitTangentMinus a b) := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hzIm : z.im ≤ -(1 / 2) := by
    simp only [z, sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_mul, mul_one, zero_sub]
    linarith
  have htrace := xiRelativeResolventTrace_im_nonneg_lowerExterior z hzIm
  have hzAbs : 1 / 2 ≤ |z.im| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hXi : XiC z ≠ 0 :=
    SlabFullWidthAdmissibility.XiC_ne_zero_of_half_le_abs_im hzAbs
  have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [thetaXiHankelOrbit_kreinForm_eq]
  rw [thetaXiHankelOrbitValuePlus, thetaXiHankelOrbitTangentPlus]
  change 0 ≤ 2 * (((starRingEnd ℂ) (XiC z)) * (-I * deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im (XiC z) (deriv XiC z) hXi]
  rw [← logDeriv_apply, hlog]
  exact mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) htrace

/-- The Hedenmalm Fourier current is globally nonnegative at every exterior aperture in the
theta-cusp Fourier strip. -/
theorem thetaCuspCenterMixedFourierCurrent_nonneg_of_half_le
    {a : ℝ} (haHalf : 1 / 2 ≤ a) (haOne : a < 1) (b : ℝ) :
    0 ≤ thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_nonneg (by linarith)]; exact haOne) b := by
  rw [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm]
  exact thetaXiHankelOrbit_kreinForm_nonneg_of_half_le haHalf b

/-- **Complete exterior Gaussian Hankel law.** At every positive Gaussian temperature and every
exterior aperture `1/2 ≤ a < 1`, all finite sections of the infinite Hedenmalm moment tower are
positive semidefinite. -/
theorem hedenmalmGaussianHankelCone_exterior
    {tau a : ℝ} (htau : 0 < tau) (haHalf : 1 / 2 ≤ a) (haOne : a < 1) :
    CompleteHankelCone
      (weightedMoment (gaussianWindowMeasure tau)
        (thetaCuspCenterMixedFourierCurrent a
          (by rw [abs_of_nonneg (by linarith)]; exact haOne))) := by
  apply (hedenmalmGaussianHankelCone_at_iff_pointwise htau
    (by rw [abs_of_nonneg (by linarith)]; exact haOne)).mpr
  exact thetaCuspCenterMixedFourierCurrent_nonneg_of_half_le haHalf haOne

/-- One canonical complete tower: the sharp strip-boundary aperture `a = 1/2` is positive at every
positive Gaussian temperature, unconditionally. -/
theorem hedenmalmGaussianHankelCone_boundary
    {tau : ℝ} (htau : 0 < tau) :
    CompleteHankelCone
      (weightedMoment (gaussianWindowMeasure tau)
        (thetaCuspCenterMixedFourierCurrent (1 / 2) (by norm_num))) := by
  exact hedenmalmGaussianHankelCone_exterior htau (by norm_num) (by norm_num)

end

end RHTower
