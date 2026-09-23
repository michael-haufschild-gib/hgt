import GaloisForLFunctions.RHTower.CCMGuinandWeilXiScrewGreenConnection
import GaloisForLFunctions.RHTower.CCMFUSuzukiPositiveMixture
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseArithmetic
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseCurvature

/-!
# Literal source bridge from CCM-FU's Xi screw to Suzuki's pointwise transport input

The CCM-FU completed third-grade route and the Riemann--Gaussian transport route
write Suzuki's nonnegative-time source in superficially different normalizations.
This module proves their literal equality.  In particular, it identifies both the
finite von-Mangoldt cutoff and the completed Gamma--Lerch sector, including the
endpoint `t = 0` of the latter's convergent series.

This is source infrastructure only.  It supplies no positivity, boundedness, or
Riemann-hypothesis assertion.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- The CCM-FU Lerch tail is the damped order-two Hurwitz--Lerch series used by
Suzuki's pointwise formula. -/
theorem screwLerchTail_eq_damped_hurwitz (t : ℝ) :
    screwLerchTail t =
      (1 / 4 : ℝ) * Real.exp (-t / 2) *
        RiemannGaussian.suzukiHurwitzLerchTwo (Real.exp (-2 * t)) := by
  unfold screwLerchTail RiemannGaussian.suzukiHurwitzLerchTwo
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [exp_neg_lerchExp_mul, lerchExp_sq]
  unfold RiemannGaussian.suzukiHurwitzLerchTwoSummand
  have hq : (k : ℝ) + 1 / 4 ≠ 0 := by positivity
  field_simp

/-- The CCM-FU endpoint constant is the undamped order-two Hurwitz--Lerch value. -/
theorem screwLerchConst_eq_hurwitz :
    screwLerchConst = (1 / 4 : ℝ) * RiemannGaussian.suzukiHurwitzLerchTwo 1 := by
  unfold screwLerchConst
  simpa using screwLerchTail_eq_damped_hurwitz 0

/-- The exact completed Gamma--Lerch memory is the nonnegative pointwise Lerch gap. -/
theorem screwLerchConst_sub_screwLerchTail_eq_pointwiseGap {t : ℝ} (ht : 0 ≤ t) :
    screwLerchConst - screwLerchTail t =
      (1 / 4 : ℝ) * ∑' n : ℕ, RiemannGaussian.suzukiPointwiseLerchGapSummand t n := by
  rw [screwLerchConst_eq_hurwitz, screwLerchTail_eq_damped_hurwitz]
  calc
    (1 / 4 : ℝ) * RiemannGaussian.suzukiHurwitzLerchTwo 1 -
        (1 / 4 : ℝ) * Real.exp (-t / 2) *
          RiemannGaussian.suzukiHurwitzLerchTwo (Real.exp (-2 * t)) =
      (1 / 4 : ℝ) *
        (RiemannGaussian.suzukiHurwitzLerchTwo 1 -
          Real.exp (-t / 2) *
            RiemannGaussian.suzukiHurwitzLerchTwo (Real.exp (-2 * t))) := by ring
    _ = (1 / 4 : ℝ) * ∑' n : ℕ,
        RiemannGaussian.suzukiPointwiseLerchGapSummand t n := by
      rw [RiemannGaussian.suzukiHurwitzLerchTwo_sub_damped_eq_tsum_gap ht]

/-- The complete CCM-FU smooth sector equals Suzuki's literal pointwise
Archimedean sector. -/
theorem ccmGuinandWeilXiScrewSmoothPart_eq_suzukiPointwiseArchimedean
    {t : ℝ} (ht : 0 ≤ t) :
    ccmGuinandWeilXiScrewSmoothPart t = RiemannGaussian.suzukiPointwiseArchimedean t := by
  rw [RiemannGaussian.suzukiPointwiseArchimedean_eq_series ht]
  unfold ccmGuinandWeilXiScrewSmoothPart
    RiemannGaussian.suzukiPointwiseArchimedeanSeries screwLinearCoeff
  calc
    4 * Real.exp (t / 2) + 4 * Real.exp (-(t / 2)) - 8 +
        ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 * t +
          screwLerchConst - screwLerchTail t =
      4 * Real.exp (t / 2) + 4 * Real.exp (-(t / 2)) - 8 +
        ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 * t +
          (screwLerchConst - screwLerchTail t) := by ring
    _ = 4 * Real.exp (t / 2) + 4 * Real.exp (-(t / 2)) - 8 +
        ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 * t +
          (1 / 4 : ℝ) * ∑' n : ℕ,
            RiemannGaussian.suzukiPointwiseLerchGapSummand t n := by
      rw [screwLerchConst_sub_screwLerchTail_eq_pointwiseGap ht]
    _ = 4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
        t / 2 * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) +
          1 / 4 * ∑' n : ℕ,
            RiemannGaussian.suzukiPointwiseLerchGapSummand t n := by ring

/-- The CCM-FU finite prime cutoff is the same `n + 2` event prefix as the
pointwise transport source. -/
theorem screwPrimeSum_eq_sum_range (t : ℝ) :
    screwPrimeSum t =
      ∑ k ∈ Finset.range (⌊Real.exp t⌋₊ - 1),
        screwPrimeWeight (k + 2) * (t - Real.log (k + 2)) := by
  unfold screwPrimeSum
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  have hcount : ⌊Real.exp t⌋₊ + 1 - 2 = ⌊Real.exp t⌋₊ - 1 := by omega
  rw [hcount]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.add_comm]
  norm_num [Nat.cast_add]

/-- The two formalizations use exactly the same finite von-Mangoldt source. -/
theorem screwPrimeSum_eq_suzukiPointwisePrimeContribution {t : ℝ} (ht : 0 ≤ t) :
    screwPrimeSum t = RiemannGaussian.suzukiPointwisePrimeContribution t := by
  rw [screwPrimeSum_eq_sum_range,
    RiemannGaussian.suzukiPointwisePrimeContribution_eq_sum_range ht]
  apply Finset.sum_congr rfl
  intro k hk
  unfold screwPrimeWeight RiemannGaussian.suzukiPointwisePrimeTerm
  norm_num [Nat.cast_add]

/-- CCM-FU's literal positive-time Xi screw is Suzuki's pointwise arithmetic
transport input, with the completed prime--polar--Gamma cancellation preserved. -/
theorem suzukiPsi_eq_riemannXiSuzukiPsiNonnegative {t : ℝ} (ht : 0 ≤ t) :
    suzukiPsi t = RiemannGaussian.riemannXiSuzukiPsiNonnegative t := by
  rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht,
    ccmGuinandWeilXiScrewSmoothPart_eq_suzukiPointwiseArchimedean ht,
    screwPrimeSum_eq_suzukiPointwisePrimeContribution ht]
  rfl

/-- The literal CCM-FU source is the exact finite-active-hinge transport model.
This identifies the transport input, but asserts neither its global nonnegativity nor a bound
on its marked FU average. -/
theorem suzukiPsi_eq_screwHingeModel {t : ℝ} (ht : 0 ≤ t) :
    suzukiPsi t =
      RiemannGaussian.screwHingeModel RiemannGaussian.suzukiPointwiseArchimedean
        RiemannGaussian.suzukiPrimeLocation RiemannGaussian.suzukiPrimeWeight t := by
  rw [suzukiPsi_eq_riemannXiSuzukiPsiNonnegative ht]
  exact RiemannGaussian.riemannXiSuzukiPsiNonnegative_eq_screwHingeModel ht

/-- **Literal CCM-FU / Suzuki transport identity.**  The whole positive marked FU reporter,
including its moving endpoint, is the same source-faithful reporter applied to Suzuki's completed
prime--polar--Gamma pointwise source.  The equality is before any sign split or estimate. -/
theorem ccmFUCentralXiScrewPositiveMixture_eq_riemannXiSuzukiPsiNonnegative
    {b H : ℝ} (hb : 0 ≤ b) (hbH : b ≤ H) :
    ccmFUCentralXiScrewPositiveMixture b H =
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        RiemannGaussian.riemannXiSuzukiPsiNonnegative t) +
      (32 / H ^ (4 : ℕ)) * RiemannGaussian.riemannXiSuzukiPsiNonnegative H := by
  unfold ccmFUCentralXiScrewPositiveMixture
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    change ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t = _
    rw [suzukiPsi_eq_riemannXiSuzukiPsiNonnegative (hb.trans ht.1)]
  · rw [suzukiPsi_eq_riemannXiSuzukiPsiNonnegative (hb.trans hbH)]

/-- The same literal FU reporter is an exact moving positive-kernel readout of the finite-active
Suzuki hinge transport.  Thus its unresolved bound is a signed, nonlocal transport problem, not a
loss from changing source coordinates. -/
theorem ccmFUCentralXiScrewPositiveMixture_eq_screwHingeReporter
    {b H : ℝ} (hb : 0 ≤ b) (hbH : b ≤ H) :
    ccmFUCentralXiScrewPositiveMixture b H =
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        RiemannGaussian.screwHingeModel RiemannGaussian.suzukiPointwiseArchimedean
          RiemannGaussian.suzukiPrimeLocation RiemannGaussian.suzukiPrimeWeight t) +
      (32 / H ^ (4 : ℕ)) *
        RiemannGaussian.screwHingeModel RiemannGaussian.suzukiPointwiseArchimedean
          RiemannGaussian.suzukiPrimeLocation RiemannGaussian.suzukiPrimeWeight H := by
  unfold ccmFUCentralXiScrewPositiveMixture
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    change ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t = _
    rw [suzukiPsi_eq_screwHingeModel (hb.trans ht.1)]
  · rw [suzukiPsi_eq_screwHingeModel (hb.trans hbH)]

end

end RHTower
