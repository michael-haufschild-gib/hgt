import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationRegularity

/-!
# The actual correlation's imaginary-axis product identity

Absolute Fubini retains both lag half-lines. The Abel source vanishes on
the nonpositive half-line, while its correlation is even.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower

private theorem expRay_norm_of_re_zero {s : ℂ} (hs : s.re = 0) (t : ℝ) :
    ‖expRay s t‖ = 1 := by
  simp [norm_expRay, hs]

private theorem expRay_sub (s : ℂ) (x t : ℝ) :
    expRay s (x - t) = expRay s x * expRay (-s) t := by
  unfold expRay
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integrable_expRay_mul {f : ℝ → ℂ} (hf : Integrable f)
    {s : ℂ} (hs : s.re = 0) : Integrable (fun t => expRay s t * f t) := by
  apply hf.mono
  · exact (show Continuous (expRay s) by unfold expRay; fun_prop).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards with t
    simp only [norm_mul, expRay_norm_of_re_zero hs, one_mul, le_refl]

private theorem profile_full_transform_eq_ray (s : ℂ) :
    (∫ t : ℝ, expRay s t * (criticalAbelLogProfile t : ℂ)) =
      criticalAbelProfileLaplace s := by
  have hf : (Ioi (0 : ℝ)).indicator
      (fun t => expRay s t * (criticalAbelLogProfile t : ℂ)) =
      fun t => expRay s t * (criticalAbelLogProfile t : ℂ) := by
    funext t
    by_cases ht : 0 < t
    · simp [ht]
    · simp [ht, criticalAbelLogProfile_zero_of_nonpos (le_of_not_gt ht)]
  rw [← hf, integral_indicator measurableSet_Ioi]
  rfl

private theorem integrable_weighted_lag_pair {s : ℂ} (hs : s.re = 0) :
    Integrable (fun z : ℝ × ℝ => expRay s z.1 *
      ((criticalAbelLogProfile (z.2 + z.1) * criticalAbelLogProfile z.2 : ℝ) : ℂ))
      (volume.prod volume) := by
  apply (integrable_criticalAbelLogProfile_lag_pair.ofReal (𝕜 := ℂ)).mono
  · exact (show Continuous (fun z : ℝ × ℝ => expRay s z.1) by
      unfold expRay; fun_prop).aestronglyMeasurable.mul
        (integrable_criticalAbelLogProfile_lag_pair.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  · filter_upwards with z
    simp only [norm_mul, expRay_norm_of_re_zero hs, one_mul,
      RCLike.norm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_mul, le_refl]

private theorem translated_weighted_profile (s : ℂ) (t : ℝ) :
    (∫ u : ℝ, expRay s u * (criticalAbelLogProfile (t + u) : ℂ)) =
      expRay (-s) t * criticalAbelProfileLaplace s := by
  have hshift := integral_add_left_eq_self (μ := volume)
    (fun x : ℝ => expRay s (x - t) * (criticalAbelLogProfile x : ℂ)) t
  simp only [add_sub_cancel_left] at hshift
  rw [hshift]
  simp_rw [expRay_sub, mul_right_comm (expRay s _) (expRay (-s) t)]
  rw [integral_mul_const, profile_full_transform_eq_ray, mul_comm]

/-- Full-line Fourier-Laplace product, with its absolute Fubini admission. -/
theorem criticalAbelLogAutocorrelation_full_transform {s : ℂ} (hs : s.re = 0) :
    (∫ u : ℝ, expRay s u * (criticalAbelLogAutocorrelation u : ℂ)) =
      criticalAbelProfileLaplace s * criticalAbelProfileLaplace (-s) := by
  have hswap := integral_integral_swap
    (f := fun u t : ℝ => expRay s u *
      ((criticalAbelLogProfile (t + u) * criticalAbelLogProfile t : ℝ) : ℂ))
    (integrable_weighted_lag_pair hs)
  have hinner (u : ℝ) :
      (∫ t : ℝ, expRay s u *
        ((criticalAbelLogProfile (t + u) * criticalAbelLogProfile t : ℝ) : ℂ)) =
      expRay s u * (criticalAbelLogAutocorrelation u : ℂ) := by
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  simp_rw [hinner] at hswap
  rw [hswap]
  simp_rw [Complex.ofReal_mul, ← mul_assoc]
  simp_rw [integral_mul_const, translated_weighted_profile]
  simp_rw [mul_right_comm (expRay (-s) _) (criticalAbelProfileLaplace s)]
  rw [integral_mul_const, profile_full_transform_eq_ray, mul_comm]

/-- Boundary identity uses both signs of the same actual correlation. -/
theorem criticalAbelCorrelationLaplace_boundary_product {s : ℂ} (hs : s.re = 0) :
    criticalAbelCorrelationLaplace s + criticalAbelCorrelationLaplace (-s) =
      criticalAbelProfileLaplace s * criticalAbelProfileLaplace (-s) := by
  have hi := integrable_expRay_mul
    (integrable_criticalAbelLogAutocorrelation.ofReal (𝕜 := ℂ)) hs
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    (μ := volume) (f := fun u : ℝ => expRay s u * (criticalAbelLogAutocorrelation u : ℂ))
    hi.integrableOn hi.integrableOn
  have hleft : (∫ u in Iic (0 : ℝ), expRay s u * (criticalAbelLogAutocorrelation u : ℂ)) =
      criticalAbelCorrelationLaplace (-s) := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [criticalAbelLogAutocorrelation_neg]
    simp only [expRay, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg, smul_eq_mul]
  rw [hleft, criticalAbelLogAutocorrelation_full_transform hs] at hsplit
  simpa only [criticalAbelCorrelationLaplace, bochnerLaplaceRay, smul_eq_mul,
    add_comm] using hsplit

end RHTower
