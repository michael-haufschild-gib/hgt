import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectFourthTraceThresholdAdvance
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyThreeSourceBudgetClosure

/-!
# Order-23 source-height exclusion and D2 threshold advance

The centered order-23 corpus separately proves a strict global fourth reciprocal-trace cap and an
atomwise lower bound throughout the squared-height annulus `[2365/16, 431/2)`. Four
FE--Schwarz copies of one off-line atom exceed the global source cap, so that annulus contains no
off-line Xi zero. Combined with the earlier lower-height exclusion, every off-line copy has
squared ordinate at least `431/2`.

The resulting verified-height band gives an explicit lower floor for the literal pure-prime D2
defect and moves its RH-equivalent tail threshold to `141799/10000`, with no native-decision
dependency.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Order-23 fourth-trace source budget excludes every off-line copy below squared height
`431/2`. -/
theorem xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves
    (q : XiZeroCopy) (hheight : (q.1 : ℂ).im ^ 2 < 431 / 2) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  by_cases hlow : (q.1 : ℂ).im ^ 2 < 2365 / 16
  · exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hlow)
  · have hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ 2 := le_of_not_gt hlow
    have huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
    have huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 :=
      xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hatom :=
      seventeen_over_eightHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyThree
        q huLower huUpper hvLower hheight
    have hquartet := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hoff
    have hsource := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
    nlinarith

/-- Equivalent positive height gap for every off-line Xi copy. -/
theorem fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    431 / 2 ≤ (q.1 : ℂ).im ^ 2 := by
  exact le_of_not_gt fun hheight =>
    hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves q hheight)

/-- Order-23 height exclusion exposed as a verified-height certificate. -/
theorem rhVerifiedThrough_of_sq_lt_fourHundredThirtyOne_halves
    (H : ℝ) (hHsq : H ^ 2 < 431 / 2) :
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
  have hsq : (q.1 : ℂ).im ^ 2 < 431 / 2 := by
    change rho.im ^ 2 < 431 / 2
    nlinarith
  have hline :=
    xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves q hsq
  simpa only [q, rhoSupport] using hline

/-- Any verified-height band above the Stirling threshold gives the same explicit literal
pure-prime D2 floor. -/
theorem primeArchLogHeightDefect_lower_of_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H) (hband : R + 1 / 2 ≤ H)
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
  have htrace :=
    continuedPrimeArchSourceRelativeTrace_im_nonpos_on_verifiedHeightBand
      H R hverified hband z hzIm hzHalf hzRe
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

/-- A verified-height certificate can remove its entire centered band from the D2 tail burden. -/
theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_rh_of_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H) (hband : R + 1 / 2 ≤ H)
    (hRlower : 233 / 20 < R) :
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
        (primeArchLogHeightDefect_lower_of_verifiedHeightBand
          H R hverified hband hqRe hqHalf hqLow hqUpper)
    · exact (min_le_left _ _).trans
        (hL q hqRe hqHalf (lt_of_not_ge hqUpper))
  · intro hRH
    obtain ⟨L, hL⟩ :=
      primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mpr
        hRH
    exact ⟨L, fun q hqRe hqHalf hqHigh =>
      hL q hqRe hqHalf (hRlower.trans hqHigh)⟩

/-- Near-maximal rational D2 threshold supplied by the kernel-clean order-23 source budget. -/
def xiOrderTwentyThreeD2Threshold : ℝ := 141799 / 10000

/-- The order-23 source budget verifies the exact centered band used by the new D2 threshold. -/
theorem rhVerifiedThrough_xiOrderTwentyThreeD2Threshold_add_half :
    RHVerifiedThrough (xiOrderTwentyThreeD2Threshold + 1 / 2) := by
  apply rhVerifiedThrough_of_sq_lt_fourHundredThirtyOne_halves
  norm_num [xiOrderTwentyThreeD2Threshold]

/-- Explicit pure-prime floor on the full newly discharged order-23 band. -/
theorem primeArchLogHeightDefect_lower_of_orderTwentyThreeBand
    {s : ℂ} (hsRe : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hsLow : 233 / 20 < s.im) (hsUpper : s.im ≤ xiOrderTwentyThreeD2Threshold) :
    -(Real.log Real.pi + Real.log 2) - 8 ≤ primeArchLogHeightDefect s := by
  exact primeArchLogHeightDefect_lower_of_verifiedHeightBand
    (xiOrderTwentyThreeD2Threshold + 1 / 2) xiOrderTwentyThreeD2Threshold
    rhVerifiedThrough_xiOrderTwentyThreeD2Threshold_add_half (by linarith)
    hsRe hsHalf hsLow hsUpper

/-- Premise-free order-23 strengthened D2 endpoint. -/
theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_xiOrderTwentyThreeThreshold_iff_rh :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow
        xiOrderTwentyThreeD2Threshold ↔ RiemannHypothesis := by
  exact
    primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_rh_of_verifiedHeightBand
      (xiOrderTwentyThreeD2Threshold + 1 / 2) xiOrderTwentyThreeD2Threshold
      rhVerifiedThrough_xiOrderTwentyThreeD2Threshold_add_half (by linarith)
      (by norm_num [xiOrderTwentyThreeD2Threshold])

end

end RHTower
