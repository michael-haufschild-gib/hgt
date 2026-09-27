import GaloisForLFunctions.RHTower.CCMThetaGroundProfile
import GaloisForLFunctions.RHTower.ThetaFullArithmeticGroundForm
import GaloisForLFunctions.RHTower.SuzukiCCMMixedPolarFactorization

/-!
# Literal theta arithmetic in the CCM correlation coordinate

For every complex smooth CCM source, the theta ground profile reconstructs
the physical source pointwise. Its continuous arithmetic density integrates
to the original compensated Gamma correlation kernel plus the two pole
translations. No evenness or reality assumption is imposed on the source.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate

namespace RHTower

open ThetaSourceWard

theorem integrable_ccmTheta_source_norm_sq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : Integrable (fun x : ℝ => ‖u x‖ ^ 2) := by
  apply (integrable_thetaGroundNormDensity (ccmThetaGroundProfile u)).congr
  exact Eventually.of_forall fun x => by
    rw [thetaGroundNormDensity_eq, ccmThetaGroundProfile_reconstruct]

theorem integrable_ccmTheta_source_cross {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    Integrable (fun x : ℝ => u (x + h) * conj (u x)) := by
  have hi : Integrable (fun x : ℝ => u (x + h)) := u.integrable.comp_add_right h
  apply hi.mul_bdd (c := ‖u.toSchwartz.toBoundedContinuousFunction‖)
    (Complex.continuous_conj.comp u.continuous).aestronglyMeasurable
  filter_upwards with x
  simpa only [Function.comp_apply, Complex.norm_conj, SchwartzMap.toBoundedContinuousFunction_apply,
    CCMComplexSmoothInteriorSource.toSchwartz_apply] using
    u.toSchwartz.toBoundedContinuousFunction.norm_coe_le_norm x

theorem ccmTheta_correlation_forward {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    ccmComplexSmoothCrossCorrelation u u h = ∫ x : ℝ, u (x + h) * conj (u x) := by
  rw [ccmComplexSmoothCrossCorrelation_apply]
  have ht := integral_add_right_eq_self (μ := volume) (fun x : ℝ => u x * conj (u (x - h))) h
  simpa only [add_sub_cancel_right, starRingEnd_apply] using ht.symm

theorem ccmTheta_correlation_zero {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    (ccmComplexSmoothCrossCorrelation u u 0).re = ∫ x : ℝ, ‖u x‖ ^ 2 := by
  rw [ccmTheta_correlation_forward]
  simp only [add_zero]
  have hi := integral_re (integrable_ccmTheta_source_cross u 0)
  simp only [RCLike.re_to_complex, add_zero] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem ccmTheta_correlation_neg_re {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    (ccmComplexSmoothCrossCorrelation u u (-h)).re =
      (ccmComplexSmoothCrossCorrelation u u h).re := by
  rw [ccmComplexSmoothCrossCorrelation_apply, ccmTheta_correlation_forward]
  simp only [sub_neg_eq_add]
  have he : (fun x : ℝ => u x * star (u (x + h))) =
      fun x : ℝ => conj (u (x + h) * conj (u x)) := by
    funext x
    simp only [map_mul, starRingEnd_apply, star_star]
    ring
  rw [he, integral_conj, Complex.conj_re]

theorem integral_ccmTheta_source_cross_re {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    (∫ x : ℝ, (u (x + h) * conj (u x)).re) = (ccmComplexSmoothCrossCorrelation u u h).re := by
  have hr := integral_re (integrable_ccmTheta_source_cross u h)
  simpa only [RCLike.re_to_complex, ← ccmTheta_correlation_forward] using hr

theorem thetaGammaPolarQuadraticDensity_ccmProfile {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h x : ℝ) :
    thetaGammaPolarQuadraticDensity thetaCuspTiltSource (ccmThetaGroundProfile u) (h, x) =
      Real.exp (-2 * h) / (1 - Real.exp (-2 * h)) * (‖u x‖ ^ 2 + ‖u (x + h)‖ ^ 2) +
        2 * thetaGammaPolarScalingKernel h * (u (x + h) * conj (u x)).re := by
  have hn (y : ℝ) : thetaCuspFullSource y ^ 2 * ‖ccmThetaGroundProfile u y‖ ^ 2 = ‖u y‖ ^ 2 := by
    rw [← thetaGroundNormDensity, thetaGroundNormDensity_eq, ccmThetaGroundProfile_reconstruct]
  have hc : thetaCuspFullSource x * thetaCuspFullSource (x + h) *
      (ccmThetaGroundProfile u (x + h) * conj (ccmThetaGroundProfile u x)).re =
        (u (x + h) * conj (u x)).re := by
    conv_rhs => rw [← ccmThetaGroundProfile_reconstruct u (x + h),
      ← ccmThetaGroundProfile_reconstruct u x]
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  simp only [thetaGammaPolarQuadraticDensity, thetaCuspTiltSource_k, hn]
  linear_combination 2 * thetaGammaPolarScalingKernel h * hc

/-- The complete continuous density integrates to the same Hermitian correlation as CCM. -/
theorem integral_thetaGammaPolarQuadraticDensity_ccmProfile {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    (∫ x : ℝ, thetaGammaPolarQuadraticDensity thetaCuspTiltSource (ccmThetaGroundProfile u) (h, x)) =
      2 * (Real.exp (-2 * h) / (1 - Real.exp (-2 * h))) *
        (ccmComplexSmoothCrossCorrelation u u 0).re +
      2 * thetaGammaPolarScalingKernel h * (ccmComplexSmoothCrossCorrelation u u h).re := by
  have hn := integrable_ccmTheta_source_norm_sq u
  have hc : Integrable (fun x : ℝ => (u (x + h) * conj (u x)).re) := by
    simpa only [RCLike.re_to_complex] using (integrable_ccmTheta_source_cross u h).re
  simp_rw [thetaGammaPolarQuadraticDensity_ccmProfile]
  rw [integral_add ((hn.fun_add (hn.comp_add_right h)).const_mul _) (hc.const_mul _),
    integral_const_mul, integral_const_mul, integral_add hn (hn.comp_add_right h),
    integral_add_right_eq_self (fun x : ℝ => ‖u x‖ ^ 2) h,
    ← ccmTheta_correlation_zero, integral_ccmTheta_source_cross_re]
  ring

/-- The singular part agrees exactly with the existing compensated Gauss kernel. -/
theorem theta_ccm_continuous_correlation_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, thetaGammaPolarQuadraticDensity thetaCuspTiltSource (ccmThetaGroundProfile u) (h, x)) =
      -(ccmArchimedeanGaussCancellationKernel (ccmComplexSmoothCrossCorrelationTest u u) h).re +
        2 * Real.cosh (h / 2) *
          (ccmComplexSmoothCrossCorrelation u u h + ccmComplexSmoothCrossCorrelation u u (-h)).re := by
  rw [integral_thetaGammaPolarQuadraticDensity_ccmProfile,
    ccmArchimedeanGaussCancellationKernel_eq _ hh]
  change _ = -(((Real.exp (-h / 2) : ℂ) *
    (ccmComplexSmoothCrossCorrelation u u h + ccmComplexSmoothCrossCorrelation u u (-h)) -
      2 * (Real.exp (-2 * h) : ℂ) * ccmComplexSmoothCrossCorrelation u u 0) /
        (1 - Real.exp (-2 * h) : ℝ)).re + _
  simp only [Complex.div_ofReal_re, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, sub_zero, add_zero, ccmTheta_correlation_neg_re, thetaGammaPolarScalingKernel]
  ring

end RHTower
