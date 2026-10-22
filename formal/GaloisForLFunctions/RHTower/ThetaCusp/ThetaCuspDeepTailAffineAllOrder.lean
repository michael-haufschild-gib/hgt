import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceRisingAbsolute
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspDeepTailCooling

open MeasureTheory
namespace RHTower
noncomputable section

/-- All-order complete deep-tail cooling at the support-sensitive threshold.
Unlike the uniform likelihood bound, the threshold grows only by one eighth
per derivative because the literal deep spectral support starts at eight. -/
theorem abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_affine
    (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hm : (n : ℝ) / 8 ≤
      thetaCuspSingleAtomReflectionScale 1 x - 49 / 20) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      (16 * thetaCuspSingleAtomReflectionScale 1 x + (n : ℝ) - 1) ^ n *
        thetaCuspDeepTailErrorScale x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  change (n : ℝ) / 8 ≤ q - 49 / 20 at hm
  have hq0 : 0 ≤ q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hcoeff : 0 ≤ 2 * q + ((n : ℝ) - 1) / 8 := by linarith
  have hscoreInt := integrable_laplaceCoolingJet_mul_exp_deep n 0 hB
  have hmomentInt := integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure n hB
  have hpoint (t : ℝ) (ht : 8 ≤ t) :
      |HTGeometry.laplaceCoolingJet n 0 (q * t)| ≤
        (2 * q + ((n : ℝ) - 1) / 8) ^ n * t ^ n := by
    have ht0 : 0 ≤ t := by linarith
    have hzt : 0 ≤ q * t := mul_nonneg hq0 ht0
    have hbase : 0 ≤ 2 * (q * t) + (n : ℝ) - 1 := by linarith
    have hdelta : 0 ≤ ((n : ℝ) - 1) * (t - 8) :=
      mul_nonneg (by linarith) (by linarith)
    have hscale : 2 * (q * t) + (n : ℝ) - 1 ≤
        (2 * q + ((n : ℝ) - 1) / 8) * t := by
      nlinarith only [hdelta]
    calc
      |HTGeometry.laplaceCoolingJet n 0 (q * t)| ≤
          (2 * (q * t) + (n : ℝ) - 1) ^ n :=
            HTGeometry.abs_laplaceCoolingJet_le_affine n hzt
      _ ≤ ((2 * q + ((n : ℝ) - 1) / 8) * t) ^ n :=
        pow_le_pow_left₀ hbase hscale n
      _ = (2 * q + ((n : ℝ) - 1) / 8) ^ n * t ^ n := mul_pow _ _ _
  have hintegral :
      |∫ t : ℝ, HTGeometry.laplaceCoolingJet n 0 (q * t) *
          Real.exp (-thetaCuspLikelihoodCoordinate x * t)
          ∂thetaCuspDeepTailSpectralMeasure| ≤
        (2 * q + ((n : ℝ) - 1) / 8) ^ n *
          thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n := by
    calc
      _ ≤ ∫ t : ℝ, ‖HTGeometry.laplaceCoolingJet n 0 (q * t) *
          Real.exp (-thetaCuspLikelihoodCoordinate x * t)‖
          ∂thetaCuspDeepTailSpectralMeasure := by
            simpa only [Real.norm_eq_abs] using
              (abs_integral_le_integral_abs
                (f := fun t : ℝ => HTGeometry.laplaceCoolingJet n 0 (q * t) *
                  Real.exp (-thetaCuspLikelihoodCoordinate x * t))
                (μ := thetaCuspDeepTailSpectralMeasure))
      _ ≤ ∫ t : ℝ, (2 * q + ((n : ℝ) - 1) / 8) ^ n *
          (t ^ n * Real.exp (-thetaCuspLikelihoodCoordinate x * t))
          ∂thetaCuspDeepTailSpectralMeasure := by
            apply integral_mono_ae hscoreInt.norm (hmomentInt.const_mul _)
            filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            have hp := mul_le_mul_of_nonneg_right (hpoint t ht)
              (Real.exp_pos (-thetaCuspLikelihoodCoordinate x * t)).le
            simpa only [mul_assoc] using hp
      _ = _ := by rw [thetaCuspDeepTailMoment, integral_const_mul]
  have htransport :
      thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n ≤
        8 ^ n * thetaCuspDeepTailErrorScale x :=
    thetaCuspDeepTailMoment_le_errorScale n hm
  rw [iteratedDeriv_thetaCuspDeepLikelihoodRemainder n hx,
    thetaCuspDeepCoolingJet_eq_integral_score n 0 hB]
  change |∫ t : ℝ, HTGeometry.laplaceCoolingJet n 0 (q * t) *
      Real.exp (-thetaCuspLikelihoodCoordinate x * t)
      ∂thetaCuspDeepTailSpectralMeasure| ≤ _
  calc
    _ ≤ (2 * q + ((n : ℝ) - 1) / 8) ^ n *
        thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n := hintegral
    _ ≤ (2 * q + ((n : ℝ) - 1) / 8) ^ n *
        (8 ^ n * thetaCuspDeepTailErrorScale x) :=
      mul_le_mul_of_nonneg_left htransport (pow_nonneg hcoeff n)
    _ = (16 * q + (n : ℝ) - 1) ^ n * thetaCuspDeepTailErrorScale x := by
      calc
        _ = ((2 * q + ((n : ℝ) - 1) / 8) * 8) ^ n *
            thetaCuspDeepTailErrorScale x := by
              rw [mul_pow]
              ring
        _ = _ := by congr 1; ring

end
end RHTower
