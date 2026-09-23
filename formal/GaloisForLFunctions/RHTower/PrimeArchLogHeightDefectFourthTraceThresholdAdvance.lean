import GaloisForLFunctions.RHTower.PrimeArchFourthTracePurePrimeTail
import GaloisForLFunctions.RHTower.PrimeArchVerifiedHeightAccretivity
import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand

/-!
# Fourth-trace threshold advance for the D2 pure-prime defect

The canonical D2 tail begins at `233 / 20`, obtained by rounding the exact fourth reciprocal-trace
zero exclusion before verified-height transfer. This module recovers the discarded algebraic
margin. Every real threshold `R > 233 / 20` satisfying
`(R + 1 / 2)^(2 : ℕ) < 2365 / 16` has an unconditional explicit defect floor on the intervening band,
so lower boundedness strictly above `R` remains equivalent to RH.

The rational threshold `58289 / 5000` satisfies the exact square inequality and yields a closed,
premise-free strengthened D2 endpoint.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Exact fourth-trace squared-height exclusion, exposed as a verified-height certificate. -/
theorem rhVerifiedThrough_of_sq_lt_2365_over_16
    (H : ℝ) (hHsq : H ^ (2 : ℕ) < 2365 / 16) :
    RHVerifiedThrough H := by
  intro rho hzero _hre0 _hre1 him0 himUpper
  let rhoSupport : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rhoSupport
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by
      omega
    exact ⟨rhoSupport, ⟨0, hn⟩⟩
  have hsq : (q.1 : ℂ).im ^ (2 : ℕ) < 2365 / 16 := by
    change rho.im ^ (2 : ℕ) < 2365 / 16
    nlinarith
  have hline := xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hsq
  simpa only [q, rhoSupport] using hline

/-- The fourth-trace exclusion gives an explicit literal pure-prime floor throughout every
newly exposed band below its exact squared-height frontier. -/
theorem primeArchLogHeightDefect_lower_of_fourthTraceBand
    (R : ℝ) (hRsq : (R + 1 / 2) ^ (2 : ℕ) < 2365 / 16)
    {s : ℂ} (hsRe : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hsLow : 233 / 20 < s.im) (hsUpper : s.im ≤ R) :
    -(Real.log Real.pi + Real.log 2) - 8 ≤ primeArchLogHeightDefect s := by
  let z : ℂ := (s.im : ℂ) + ((1 / 2 - s.re : ℝ) : ℂ) * I
  have hzIm : 0 < z.im := by
    simp only [z, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_add, zero_mul, mul_one]
    linarith
  have hzHalf : z.im < 1 / 2 := by
    simp only [z, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_add, zero_mul, mul_one]
    linarith
  have hzRe : |z.re| ≤ R := by
    simp only [z, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    rw [abs_of_pos (by linarith : 0 < s.im)]
    exact hsUpper
  have hcoord : (1 / 2 : ℂ) + z * I = s := by
    apply Complex.ext <;>
      simp [z, Complex.mul_re, Complex.mul_im]
  have hverified : RHVerifiedThrough (R + 1 / 2) :=
    rhVerifiedThrough_of_sq_lt_2365_over_16 (R + 1 / 2) hRsq
  have htrace :=
    continuedPrimeArchSourceRelativeTrace_im_nonpos_on_verifiedHeightBand
      (R + 1 / 2) R hverified (by linarith) z hzIm hzHalf hzRe
  rw [continuedPrimeArchSourceRelativeTrace, hcoord] at htrace
  have hcompleted :
      0 ≤ (infinitePrimeFlux s - logDeriv archFactor s).re := by
    simp only [Complex.mul_im, Complex.neg_im, I_re, I_im,
      zero_mul, neg_mul, one_mul] at htrace
    linarith
  have harch :=
    abs_re_logDeriv_archFactor_sub_primeArchHighFrequencyMainTerm_le_four
      hsRe hsHalf hsLow
  rw [abs_le] at harch
  have hmain :=
    (primeArchHighFrequencyMainTerm_sub_heightMainTerm_nonneg_le_one
      hsRe hsHalf hsLow).1
  have hheight := primeArchHighFrequencyHeightMainTerm_eq_half_log_sub_constant
    (t := s.im) (by linarith)
  rw [hheight] at hmain
  rw [primeArchLogHeightDefect]
  simp only [Complex.sub_re] at hcompleted
  linarith

/-- Every exact fourth-trace band can be removed from the remaining D2 tail burden. -/
theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_rh_of_fourthTraceBand
    (R : ℝ) (hRlower : 233 / 20 < R)
    (hRsq : (R + 1 / 2) ^ (2 : ℕ) < 2365 / 16) :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow R ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨L, hL⟩
    apply
      primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mp
    refine ⟨min L (-(Real.log Real.pi + Real.log 2) - 8), ?_⟩
    intro q hqRe hqHalf hqLow
    by_cases hqUpper : (gaussianRatPoint q).im ≤ R
    · exact (min_le_right _ _).trans
        (primeArchLogHeightDefect_lower_of_fourthTraceBand
          R hRsq hqRe hqHalf hqLow hqUpper)
    · exact (min_le_left _ _).trans
        (hL q hqRe hqHalf (lt_of_not_ge hqUpper))
  · intro hRH
    obtain ⟨L, hL⟩ :=
      primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mpr
        hRH
    exact ⟨L, fun q hqRe hqHalf hqHigh =>
      hL q hqRe hqHalf (hRlower.trans hqHigh)⟩

/-- Exact rational threshold recovering nearly all margin in the fourth-trace square bound. -/
def xiFourthTraceD2Threshold : ℝ := 58289 / 5000

/-- Premise-free strengthened D2 endpoint at `58289/5000 > 233/20`. -/
theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_xiFourthTraceThreshold_iff_rh :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow
        xiFourthTraceD2Threshold ↔ RiemannHypothesis := by
  apply
    primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_rh_of_fourthTraceBand
  · norm_num [xiFourthTraceD2Threshold]
  · norm_num [xiFourthTraceD2Threshold]

end

end RHTower
