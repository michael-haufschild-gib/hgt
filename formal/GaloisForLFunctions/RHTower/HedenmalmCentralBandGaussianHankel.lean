import GaloisForLFunctions.RHTower.HedenmalmExteriorGaussianHankel
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity

/-!
# Unconditional complete Hedenmalm towers on the central frequency band

The exact endpoint quartet budget gives the correct relative-resolvent sign on every band
`|b| ≤ R` satisfying `C * ((R + 1/2)^2 + 1) < 4`, at every positive aperture.  Schwarz reflection
transports the upper-half-plane sign to the lower point used by the Hedenmalm current.  Restricting
a Gaussian window to that band then gives a complete all-order Hankel cone at every aperture in
the theta Fourier strip, with no Riemann-hypothesis assumption.  The concrete radius `218 / 25`
is an unconditional specialization.

This theorem does not assert global frequency positivity.  It isolates the two high-frequency
tails as the exact remaining part of the Hedenmalm condition.
-/

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Schwarz reflection turns the unconditional upper central-band anti-Herglotz sign into the
lower-half-plane Herglotz sign used by the Hedenmalm current. -/
theorem xiRelativeResolventTrace_im_nonneg_lower_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {a b : ℝ} (ha : 0 < a) (hb : |b| ≤ R) :
    0 ≤ (xiRelativeResolventTrace ((b : ℂ) - (a : ℂ) * I)).im := by
  let zminus : ℂ := (b : ℂ) - (a : ℂ) * I
  let zplus : ℂ := (b : ℂ) + (a : ℂ) * I
  have hzplusIm : 0 < zplus.im := by
    simp only [zplus, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_add, zero_mul, mul_one]
    linarith
  have hzplusRe : |zplus.re| ≤ R := by
    simpa only [zplus, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hb
  have hupper := xiRelativeResolventTrace_im_nonpos_exactOffLineQuartetBand
    R hband zplus hzplusIm hzplusRe
  have hconj : (starRingEnd ℂ) zminus = zplus := by
    apply Complex.ext <;>
      simp [zminus, zplus, mul_re, mul_im]
  have hreflect := xiRelativeResolventTrace_conj zminus
  rw [hconj] at hreflect
  rw [hreflect] at hupper
  simp only [Complex.conj_im] at hupper
  linarith

/-- The actual theta/Xi Hedenmalm orbit lies in the nonnegative Krein chamber throughout the
complete source-pure central frequency band. -/
theorem thetaXiHankelOrbit_kreinForm_nonneg_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {a b : ℝ} (ha : 0 < a) (hb : |b| ≤ R) :
    0 ≤ hedenmalmHankelKreinForm
      (thetaXiHankelOrbitValuePlus a b)
      (thetaXiHankelOrbitTangentPlus a b)
      (thetaXiHankelOrbitValueMinus a b)
      (thetaXiHankelOrbitTangentMinus a b) := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have htrace := xiRelativeResolventTrace_im_nonneg_lower_exactOffLineQuartetBand
    R hband ha hb
  let zplus : ℂ := (b : ℂ) + (a : ℂ) * I
  have hzplusIm : 0 < zplus.im := by
    simp only [zplus, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_add, zero_mul, mul_one]
    linarith
  have hzplusRe : |zplus.re| ≤ R := by
    simpa only [zplus, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hb
  have hXiPlus : XiC zplus ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand
      R hband zplus hzplusIm hzplusRe
  have hconj : (starRingEnd ℂ) zplus = z := by
    apply Complex.ext <;>
      simp [z, zplus, mul_re, mul_im]
  have hXi : XiC z ≠ 0 := by
    simpa only [hconj] using XiC_ne_zero_conj hXiPlus
  have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [thetaXiHankelOrbit_kreinForm_eq]
  rw [thetaXiHankelOrbitValuePlus, thetaXiHankelOrbitTangentPlus]
  change 0 ≤ 2 * (((starRingEnd ℂ) (XiC z)) * (-I * deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im (XiC z) (deriv XiC z) hXi]
  rw [← logDeriv_apply, hlog]
  exact mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) htrace

/-- **Interior central-band current law.**  At every positive aperture in the theta Fourier
strip, the Hedenmalm current is nonnegative throughout every exact endpoint-quartet band. -/
theorem thetaCuspCenterMixedFourierCurrent_nonneg_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) {b : ℝ} (hb : |b| ≤ R) :
    0 ≤ thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_pos ha]; exact haOne) b := by
  rw [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm]
  exact thetaXiHankelOrbit_kreinForm_nonneg_exactOffLineQuartetBand
    R hband ha hb

/-- Concrete current positivity on the full rational band supplied by the exact endpoint quartet
budget. -/
theorem thetaCuspCenterMixedFourierCurrent_nonneg_twoHundredEighteen_twentyFifths
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) {b : ℝ}
    (hb : |b| ≤ 218 / 25) :
    0 ≤ thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_pos ha]; exact haOne) b := by
  exact thetaCuspCenterMixedFourierCurrent_nonneg_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
    ha haOne hb

/-- Restriction preserves an entire bilateral exponential-moment window. -/
theorem HasEntireExponentialMoments.restrict
    {mu : Measure ℝ} (hmu : HasEntireExponentialMoments mu) (s : Set ℝ) :
    HasEntireExponentialMoments (mu.restrict s) := by
  apply Set.eq_univ_of_forall
  intro t
  apply (integrable_of_mem_integrableExpSet (by rw [hmu]; exact Set.mem_univ t)).mono_measure
  exact Measure.restrict_le_self

/-- Gaussian measure restricted to the unconditional centered Xi frequency band. -/
def hedenmalmCentralGaussianMeasure (tau R : ℝ) : Measure ℝ :=
  (gaussianWindowMeasure tau).restrict (Set.Icc (-R) R)

/-- **Complete interior central-band Gaussian Hankel law.**  At every positive Gaussian
temperature and every positive aperture in the theta Fourier strip, all finite sections of the
restricted moment tower are positive semidefinite simultaneously. -/
theorem hedenmalmCentralGaussianHankelCone_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {tau a : ℝ} (htau : 0 < tau) (ha : 0 < a) (haOne : a < 1) :
    CompleteHankelCone
      (weightedMoment (hedenmalmCentralGaussianMeasure tau R)
        (thetaCuspCenterMixedFourierCurrent a
          (by rw [abs_of_pos ha]; exact haOne))) := by
  letI := gaussianWindowMeasure_finite htau
  letI : IsFiniteMeasure (hedenmalmCentralGaussianMeasure tau R) := by
    rw [hedenmalmCentralGaussianMeasure]
    infer_instance
  let J : ℝ → ℝ := thetaCuspCenterMixedFourierCurrent a
    (by rw [abs_of_pos ha]; exact haOne)
  have hmu : HasEntireExponentialMoments (hedenmalmCentralGaussianMeasure tau R) := by
    exact (gaussianWindowMeasure_hasEntireExponentialMoments htau).restrict _
  have hJ : MemLp J ∞ (hedenmalmCentralGaussianMeasure tau R) := by
    apply MemLp.mono_measure Measure.restrict_le_self
    exact thetaCuspCenterMixedFourierCurrent_memLp_top tau a
      (by rw [abs_of_pos ha]; exact haOne)
  apply (completeHankelCone_weightedMoment_iff_ae hmu J hJ).2
  filter_upwards [ae_restrict_mem measurableSet_Icc] with b hb
  exact thetaCuspCenterMixedFourierCurrent_nonneg_exactOffLineQuartetBand
    R hband ha haOne (abs_le.mpr hb)

/-- The complete Gaussian Hankel tower on the full rational endpoint-quartet band. -/
theorem hedenmalmCentralGaussianHankelCone_twoHundredEighteen_twentyFifths
    {tau a : ℝ} (htau : 0 < tau) (ha : 0 < a) (haOne : a < 1) :
    CompleteHankelCone
      (weightedMoment (hedenmalmCentralGaussianMeasure tau (218 / 25))
        (thetaCuspCenterMixedFourierCurrent a
          (by rw [abs_of_pos ha]; exact haOne))) := by
  exact hedenmalmCentralGaussianHankelCone_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
    htau ha haOne

end

end RHTower
