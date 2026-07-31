import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetHalfLine
import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicRelativeRemainder
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteCoefficientGate

/-!
# Canonical untruncated theta-tail/seam Prouhet current bound

This module instantiates the self-consistent phase-adapted packet with the full positive-half-line
canonical density transform and the exact half-exponential seam.  The Haar depth is selected
separately at each spectral point.  At that depth the signed off-diagonal untruncated current is
identically zero, and hence is strictly sublinear relative to the final scheduled Taylor section.
-/

open Complex Real Polynomial MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Full positive-half-line value transform of the exact canonical density. -/
def thetaCuspTailSecondDensityPhaseValue (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z

/-- Spectral derivative of the full positive-half-line canonical density transform. -/
def thetaCuspTailSecondDensityPhaseDerivative (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z)

/-- The endpoint chosen from the actual density and exact half-exponential seam data. -/
def canonicalThetaTailSeamProuhetEndpoint
    (m N : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedCriticalSelfConsistentEndpoint m N
    (spectralTranslationPhase (Real.log 2) z)
    dyadicProuhetGrowthCharacter z
    (thetaCuspTailSecondDensityPhaseValue z)
    (thetaCuspTailSecondDensityPhaseDerivative z)
    (thetaHalfExponentialPhaseValue z)
    (thetaHalfExponentialPhaseDerivative z)

/-- Signed off-diagonal current of the complete untruncated canonical theta-tail/seam packet. -/
def canonicalThetaTailSeamProuhetUntruncatedCurrent
    (m N : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedCriticalReturnedSourceCurrent m N
    (spectralTranslationPhase (Real.log 2) z)
    dyadicProuhetGrowthCharacter
    (canonicalThetaTailSeamProuhetEndpoint m N z) z
    (thetaCuspTailSecondDensityPhaseValue z)
    (thetaCuspTailSecondDensityPhaseDerivative z)
    (thetaHalfExponentialPhaseValue z)
    (thetaHalfExponentialPhaseDerivative z)

/-- At every point in the open canonical Fourier strip there is a finite Haar depth at which the
complete untruncated canonical mixed current cancels exactly. -/
theorem exists_canonicalThetaTailSeamProuhetUntruncatedCurrent_eq_zero
    (m : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2) :
    ∃ N : ℕ,
      canonicalThetaTailSeamProuhetUntruncatedCurrent m N z = 0 := by
  have hQ : (thetaHalfExponentialPhaseDerivative z *
      (starRingEnd ℂ) (thetaHalfExponentialPhaseValue z)).im ≠ 0 :=
    thetaHalfExponentialPhaseCurrent_ne_zero (by linarith)
  have hden := phaseAdaptedCriticalSelfConsistentDenominator_eventually_ne_zero
    m (spectralTranslationPhase (Real.log 2) z)
    dyadicProuhetGrowthCharacter hzHalf
    (thetaHalfExponentialPhaseValue z)
    (thetaHalfExponentialPhaseDerivative z) hQ
  obtain ⟨N, hN⟩ := hden.exists
  refine ⟨N, ?_⟩
  unfold canonicalThetaTailSeamProuhetUntruncatedCurrent
    canonicalThetaTailSeamProuhetEndpoint
  exact phaseAdaptedCriticalSelfConsistentEndpoint_cancels
    m N (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaCuspTailSecondDensityPhaseValue z)
      (thetaCuspTailSecondDensityPhaseDerivative z)
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) hN

theorem eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half
    (sigma : ℂ) (hsigma : 0 < sigma.re) :
    ∀ᶠ n : ℕ in atTop,
      (xiCTaylorAnisotropicCenteredPoint sigma n).im < 1 / 2 := by
  have htend := tendsto_xiCTaylorAnisotropicCenteredPoint sigma
  have him : Tendsto (fun n => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      atTop (nhds (xiCTaylorCenteredPoint sigma).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp htend
  have htarget : (xiCTaylorCenteredPoint sigma).im < 1 / 2 := by
    rw [xiCTaylorCenteredPoint, mul_im]
    simp only [sub_re, neg_re, I_re, neg_im, I_im]
    norm_num
    linarith
  exact him.eventually (eventually_lt_nhds htarget)

/-- **Canonical untruncated current bound.**  For every admissible anisotropic schedule and every
packet order (which may vary with the mesh point), one may choose the finite Haar depth separately
at each scheduled point so that the complete signed theta-tail/seam mixed current is strictly
smaller than `epsilon * (n+1)` times the squared final Taylor value. -/
theorem eventually_exists_canonicalThetaTailSeamProuhetUntruncatedCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) (hsigma0 : 0 < sigma.re) (hsigmaHalf : sigma.re < 1 / 2)
    (m : ℕ → ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∃ N : ℕ,
      canonicalThetaTailSeamProuhetUntruncatedCurrent
          (m n) N (xiCTaylorAnisotropicCenteredPoint sigma n) <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have hzero : Tendsto (fun n : ℕ =>
      (0 : ℝ) * (((n + 1 : ℕ) : ℝ) ^
        (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
    simp
  have hpositive :=
    eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
      hD sigma (fun _ : ℕ => (0 : ℝ)) hzero hepsilon
  have himPos :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  have himHalf :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half sigma hsigma0
  filter_upwards [hpositive, himPos, himHalf] with n hn hzn0 hznHalf
  obtain ⟨N, hcurrent⟩ :=
    exists_canonicalThetaTailSeamProuhetUntruncatedCurrent_eq_zero
      (m n) hzn0 hznHalf
  refine ⟨N, ?_⟩
  rw [hcurrent]
  simpa only [zero_mul] using hn

end

end RHTower
