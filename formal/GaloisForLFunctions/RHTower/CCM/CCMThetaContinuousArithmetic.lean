import GaloisForLFunctions.RHTower.CCM.CCMThetaArithmeticCorrelation

/-!
# Complete continuous arithmetic equals the CCM Gamma and pole terms

The entire positive shift ray is integrated before using compact support to
truncate the pole correlation. The singular Gauss kernel stays compensated.
-/

noncomputable section

open MeasureTheory Filter Set

namespace RHTower

open ThetaSourceWard

def ccmThetaPolarCorrelation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) : ℂ :=
  (ccmComplexSmoothCrossCorrelation u u h + ccmComplexSmoothCrossCorrelation u u (-h)) *
    (2 * Real.cosh (h / 2) : ℂ)

theorem ccmThetaPolarCorrelation_eq_zero {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {h : ℝ} (hh : 2 * a.1 ≤ |h|) :
    ccmThetaPolarCorrelation u h = 0 := by
  unfold ccmThetaPolarCorrelation
  rw [ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs u u hh,
    ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs u u (by simpa only [abs_neg] using hh),
    add_zero, zero_mul]

theorem integrable_ccmThetaPolarCorrelation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : Integrable (ccmThetaPolarCorrelation u) := by
  have hc := (ccmComplexSmoothCrossCorrelation u u).continuous
  have hp : Continuous (ccmThetaPolarCorrelation u) := by unfold ccmThetaPolarCorrelation; fun_prop
  apply hp.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-(2 * a.1)) (2 * a.1)) isCompact_Icc
  intro h hh
  have hs : |h| < 2 * a.1 := by
    by_contra hn
    exact hh (ccmThetaPolarCorrelation_eq_zero u (le_of_not_gt hn))
  exact ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩

theorem integral_ccmThetaPolarCorrelation_Ioi {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    (∫ h in Ioi (0 : ℝ), ccmThetaPolarCorrelation u h) =
      ∫ h in Ioc (0 : ℝ) (2 * a.1), ccmThetaPolarCorrelation u h := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with h
  by_cases hh : 0 < h
  · rw [indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hh)]
    by_cases ha : h ≤ 2 * a.1
    · rw [indicator_of_mem (show h ∈ Ioc (0 : ℝ) (2 * a.1) from ⟨hh, ha⟩)]
    · rw [indicator_of_notMem (show h ∉ Ioc (0 : ℝ) (2 * a.1) from fun hm => ha hm.2)]
      exact ccmThetaPolarCorrelation_eq_zero u ((le_of_not_ge ha).trans (le_abs_self h))
  · rw [indicator_of_notMem (show h ∉ Ioi (0 : ℝ) from hh),
      indicator_of_notMem (show h ∉ Ioc (0 : ℝ) (2 * a.1) from fun hm => hh hm.1)]

/-- Every term in this Gamma--pole decomposition is an absolutely convergent integral. -/
theorem integral_thetaGammaPolarQuadraticDensity_ccmSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource (ccmThetaGroundProfile u) p
      ∂thetaContinuousLinkMeasure) =
      -(∫ h in Ioi (0 : ℝ),
        ccmArchimedeanGaussCancellationKernel (ccmComplexSmoothCrossCorrelationTest u u) h).re +
        (∫ h in Ioc (0 : ℝ) (2 * a.1), ccmThetaPolarCorrelation u h).re := by
  have hg := integrableOn_ccmArchimedeanGaussCancellationKernel (ccmComplexSmoothCrossCorrelationTest u u)
  have hp := (integrable_ccmThetaPolarCorrelation u).integrableOn (s := Ioi (0 : ℝ))
  have hgr : IntegrableOn (fun h =>
      (ccmArchimedeanGaussCancellationKernel (ccmComplexSmoothCrossCorrelationTest u u) h).re)
      (Ioi (0 : ℝ)) := by
    change Integrable (fun h : ℝ =>
      (ccmArchimedeanGaussCancellationKernel (ccmComplexSmoothCrossCorrelationTest u u) h).re)
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [RCLike.re_to_complex] using hg.re
  have hpr : IntegrableOn (fun h => (ccmThetaPolarCorrelation u h).re) (Ioi (0 : ℝ)) := by
    change Integrable (fun h : ℝ => (ccmThetaPolarCorrelation u h).re) (volume.restrict (Ioi (0 : ℝ)))
    simpa only [RCLike.re_to_complex] using hp.re
  have hgn : IntegrableOn (fun h =>
      -(ccmArchimedeanGaussCancellationKernel (ccmComplexSmoothCrossCorrelationTest u u) h).re)
      (Ioi (0 : ℝ)) := hgr.neg
  rw [integral_prod _ (integrable_thetaGammaPolarQuadraticDensity (ccmThetaGroundProfile u))]
  have he : (∫ h in Ioi (0 : ℝ), ∫ x : ℝ,
      thetaGammaPolarQuadraticDensity thetaCuspTiltSource (ccmThetaGroundProfile u) (h, x)) =
      ∫ h in Ioi (0 : ℝ),
        -(ccmArchimedeanGaussCancellationKernel (ccmComplexSmoothCrossCorrelationTest u u) h).re +
          (ccmThetaPolarCorrelation u h).re := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rw [theta_ccm_continuous_correlation_eq u hh]
    simp only [ccmThetaPolarCorrelation, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, sub_zero]
    ring
  rw [he, integral_add hgn hpr, integral_neg]
  have h₁ := integral_re hg
  have h₂ := integral_re hp
  simp only [RCLike.re_to_complex] at h₁ h₂
  rw [h₁, h₂, integral_ccmThetaPolarCorrelation_Ioi]

/-- The archimedean constant is exactly the constant in the corpus's Gauss distribution. -/
theorem theta_archConstant_ccmGroundNorm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    2 * archConstant.re * thetaGroundNormSq (ccmThetaGroundProfile u) =
      (((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        ccmComplexSmoothCrossCorrelation u u 0).re := by
  have hn : thetaGroundNormSq (ccmThetaGroundProfile u) =
      (ccmComplexSmoothCrossCorrelation u u 0).re := by
    rw [ccmTheta_correlation_zero, thetaGroundNormSq]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      rw [thetaGroundNormDensity_eq, ccmThetaGroundProfile_reconstruct]
  rw [hn]
  simp only [archConstant, Complex.div_ofNat_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  ring

/-- The entire continuous theta form is precisely polar correlation minus the CCM archimedean distribution. -/
theorem thetaGammaPolarQuadratic_ccmSource_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource (ccmThetaGroundProfile u) p
        ∂thetaContinuousLinkMeasure) - 2 * archConstant.re * thetaGroundNormSq (ccmThetaGroundProfile u) =
      ((∫ h in Ioc (0 : ℝ) (2 * a.1), ccmThetaPolarCorrelation u h) -
        ccmArchimedeanWeilDistribution (ccmComplexSmoothCrossCorrelationTest u u)).re := by
  rw [integral_thetaGammaPolarQuadraticDensity_ccmSource, theta_archConstant_ccmGroundNorm,
    ← ccmGaussCancellation_constant_eq_weilDistribution, Complex.sub_re, Complex.add_re]
  change _ = (∫ h in Ioc (0 : ℝ) (2 * a.1), ccmThetaPolarCorrelation u h).re -
    ((((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) *
      ccmComplexSmoothCrossCorrelation u u 0).re + _)
  ring

end RHTower
