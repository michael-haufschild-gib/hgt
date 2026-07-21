import GaloisForLFunctions.RHTower.HedenmalmExteriorGaussianHankel
import GaloisForLFunctions.RHTower.PrimeArchHighFrequencyAccretivity

/-!
# Unconditional complete Hedenmalm towers on the central frequency band

The source-pure Xi height gap gives the correct relative-resolvent sign on `|b| ≤ 4` at every
positive aperture.  Schwarz reflection transports the upper-half-plane sign to the lower point
used by the Hedenmalm current.  Restricting a Gaussian window to that band then gives a complete
all-order Hankel cone at every critical aperture, with no Riemann-hypothesis assumption.

This theorem does not assert global frequency positivity.  It isolates the two high-frequency
tails as the exact remaining part of the Hedenmalm condition.
-/

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Schwarz reflection turns the unconditional upper central-band anti-Herglotz sign into the
lower-half-plane Herglotz sign used by the Hedenmalm current. -/
theorem xiRelativeResolventTrace_im_nonneg_lowerCentralBand
    {a b : ℝ} (ha : 0 < a) (hb : |b| ≤ 4) :
    0 ≤ (xiRelativeResolventTrace ((b : ℂ) - (a : ℂ) * I)).im := by
  let zminus : ℂ := (b : ℂ) - (a : ℂ) * I
  let zplus : ℂ := (b : ℂ) + (a : ℂ) * I
  have hzplusIm : 0 < zplus.im := by
    simp only [zplus, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_add, zero_mul, mul_one]
    linarith
  have hzplusRe : |zplus.re| ≤ 4 := by
    simpa only [zplus, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hb
  have hupper := xiRelativeResolventTrace_im_nonpos_lowFrequency
    4 (by norm_num) (by norm_num) zplus hzplusIm hzplusRe
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
theorem thetaXiHankelOrbit_kreinForm_nonneg_centralBand
    {a b : ℝ} (ha : 0 < a) (hb : |b| ≤ 4) :
    0 ≤ hedenmalmHankelKreinForm
      (thetaXiHankelOrbitValuePlus a b)
      (thetaXiHankelOrbitTangentPlus a b)
      (thetaXiHankelOrbitValueMinus a b)
      (thetaXiHankelOrbitTangentMinus a b) := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have htrace := xiRelativeResolventTrace_im_nonneg_lowerCentralBand ha hb
  have hzRe : |z.re| ≤ 4 := by
    simpa only [z, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero] using hb
  have hXi : XiC z ≠ 0 := XiC_ne_zero_of_abs_re_le_four hzRe
  have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [thetaXiHankelOrbit_kreinForm_eq]
  rw [thetaXiHankelOrbitValuePlus, thetaXiHankelOrbitTangentPlus]
  change 0 ≤ 2 * (((starRingEnd ℂ) (XiC z)) * (-I * deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im (XiC z) (deriv XiC z) hXi]
  rw [← logDeriv_apply, hlog]
  exact mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) htrace

/-- **Interior central-band current law.**  At every positive aperture in the theta Fourier
strip, the Hedenmalm current is nonnegative throughout `|b| ≤ 4`. -/
theorem thetaCuspCenterMixedFourierCurrent_nonneg_centralBand
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) {b : ℝ} (hb : |b| ≤ 4) :
    0 ≤ thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_pos ha]; exact haOne) b := by
  rw [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm]
  exact thetaXiHankelOrbit_kreinForm_nonneg_centralBand ha hb

/-- Restriction preserves an entire bilateral exponential-moment window. -/
theorem HasEntireExponentialMoments.restrict
    {mu : Measure ℝ} (hmu : HasEntireExponentialMoments mu) (s : Set ℝ) :
    HasEntireExponentialMoments (mu.restrict s) := by
  apply Set.eq_univ_of_forall
  intro t
  apply (integrable_of_mem_integrableExpSet (by rw [hmu]; exact Set.mem_univ t)).mono_measure
  exact Measure.restrict_le_self

/-- Gaussian measure restricted to the unconditional centered Xi frequency band. -/
def hedenmalmCentralGaussianMeasure (tau : ℝ) : Measure ℝ :=
  (gaussianWindowMeasure tau).restrict (Set.Icc (-4) 4)

/-- **Complete interior central-band Gaussian Hankel law.**  At every positive Gaussian
temperature and every critical aperture, all finite sections of the restricted moment tower are
positive semidefinite simultaneously. -/
theorem hedenmalmCentralGaussianHankelCone
    {tau a : ℝ} (htau : 0 < tau) (ha : 0 < a) (haHalf : a < 1 / 2) :
    CompleteHankelCone
      (weightedMoment (hedenmalmCentralGaussianMeasure tau)
        (thetaCuspCenterMixedFourierCurrent a
          (by rw [abs_of_pos ha]; linarith))) := by
  letI := gaussianWindowMeasure_finite htau
  letI : IsFiniteMeasure (hedenmalmCentralGaussianMeasure tau) := by
    rw [hedenmalmCentralGaussianMeasure]
    infer_instance
  let J : ℝ → ℝ := thetaCuspCenterMixedFourierCurrent a
    (by rw [abs_of_pos ha]; linarith)
  have hmu : HasEntireExponentialMoments (hedenmalmCentralGaussianMeasure tau) := by
    exact (gaussianWindowMeasure_hasEntireExponentialMoments htau).restrict _
  have hJ : MemLp J ∞ (hedenmalmCentralGaussianMeasure tau) := by
    apply MemLp.mono_measure Measure.restrict_le_self
    exact thetaCuspCenterMixedFourierCurrent_memLp_top tau a
      (by rw [abs_of_pos ha]; linarith)
  apply (completeHankelCone_weightedMoment_iff_ae hmu J hJ).2
  filter_upwards [ae_restrict_mem measurableSet_Icc] with b hb
  exact thetaCuspCenterMixedFourierCurrent_nonneg_centralBand ha (by linarith)
    (abs_le.mpr hb)

end

end RHTower
