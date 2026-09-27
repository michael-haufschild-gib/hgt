import GaloisForLFunctions.RHTower.ThetaGammaPolarDiagonalIntegral

/-!
# The complete literal arithmetic form in theta ground coordinates

The continuous quadratic density retains the compensated Gamma term and both
polar translations. After subtracting the archimedean constant and the prime
cross pairing, its value is exactly prime jump energy minus continuous jump
energy. Every displayed integral is absolutely convergent.

This supplies a literal arithmetic form identity. Equality with the existing
CCM restricted Weil form is a further comparison, not an assumption here.
-/

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

def thetaGroundNormDensity (chi : 𝓢(ℝ, ℂ)) (x : ℝ) : ℝ :=
  thetaCuspFullSource x ^ 2 * ‖chi x‖ ^ 2

def thetaGroundNormSq (chi : 𝓢(ℝ, ℂ)) : ℝ := ∫ x : ℝ, thetaGroundNormDensity chi x

theorem thetaGroundNormDensity_eq (chi : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaGroundNormDensity chi x = ‖(thetaCuspFullSource x : ℂ) * chi x‖ ^ 2 := by
  simp only [thetaGroundNormDensity, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

theorem integrable_thetaGroundNormDensity (chi : 𝓢(ℝ, ℂ)) :
    Integrable (thetaGroundNormDensity chi) := by
  let N := ‖chi.toBoundedContinuousFunction‖
  have hi : Integrable (fun x : ℝ => ‖chi x‖ ^ 2) := by
    have h := (chi.integrable (μ := volume)).norm.mul_bdd (c := N) chi.continuous.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [N, norm_norm, SchwartzMap.toBoundedContinuousFunction_apply] using
          chi.toBoundedContinuousFunction.norm_coe_le_norm x)
    simpa only [pow_two] using h
  have hC := thetaCuspDerivativeExpConstant_nonneg 0
  have hk := contDiff_thetaCuspFullSource.continuous
  apply (hi.const_mul (thetaCuspDerivativeExpConstant 0 ^ 2)).mono'
    (by unfold thetaGroundNormDensity; fun_prop)
  filter_upwards with x
  rw [thetaGroundNormDensity, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [← sq_abs (thetaCuspFullSource x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_theta_le_const x) 2

/-- Absolute convergence includes the literal continuous quadratic, before ground subtraction. -/
theorem integrable_thetaGammaPolarQuadraticDensity (chi : 𝓢(ℝ, ℂ)) :
    Integrable (thetaGammaPolarQuadraticDensity thetaCuspTiltSource chi) thetaContinuousLinkMeasure := by
  have h := (integrable_thetaGammaPolar_ground_difference thetaCuspTiltSource chi).fun_add
    (integrable_thetaGammaPolarDiagonalDensity chi)
  simpa only [sub_add_cancel] using h

theorem integral_thetaGammaPolarDiagonalDensity_eq_prime (chi : 𝓢(ℝ, ℂ)) :
    (∫ p, thetaGammaPolarDiagonalDensity thetaCuspTiltSource chi p ∂thetaContinuousLinkMeasure) =
      thetaPrimeGammaScalingDiagonal chi.toBoundedContinuousFunction +
        2 * archConstant.re * thetaGroundNormSq chi := by
  have hf : Integrable (fun x : ℝ => thetaCuspFullSource x *
      (thetaArchimedeanShiftSource x).re * ‖chi x‖ ^ 2) :=
    integrable_thetaGammaPolarSourceMarginal chi false
  have hb : Integrable (fun x : ℝ => thetaCuspFullSource x *
      (thetaArchimedeanShiftSource (-x)).re * ‖chi x‖ ^ 2) :=
    integrable_thetaGammaPolarSourceMarginal chi true
  have he (x : ℝ) : ‖chi x‖ ^ 2 * ((thetaCuspFullSource x : ℂ) *
      (thetaArchimedeanShiftSource x + thetaArchimedeanShiftSource (-x) -
        2 * archConstant * (thetaCuspFullSource x : ℂ))).re =
      (thetaCuspFullSource x * (thetaArchimedeanShiftSource x).re * ‖chi x‖ ^ 2 +
        thetaCuspFullSource x * (thetaArchimedeanShiftSource (-x)).re * ‖chi x‖ ^ 2) -
          2 * archConstant.re * thetaGroundNormDensity chi x := by
    simp only [thetaGroundNormDensity, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, sub_zero, add_zero]
    ring
  unfold thetaPrimeGammaScalingDiagonal
  simp_rw [SchwartzMap.toBoundedContinuousFunction_apply, he]
  rw [integral_sub (hf.fun_add hb) ((integrable_thetaGroundNormDensity chi).const_mul _),
    integral_add hf hb, integral_const_mul, integral_thetaGammaPolarDiagonalDensity]
  unfold thetaGroundNormSq
  ring

def thetaFullArithmeticQuadratic (chi : 𝓢(ℝ, ℂ)) : ℝ :=
  (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource chi p ∂thetaContinuousLinkMeasure) -
    2 * archConstant.re * thetaGroundNormSq chi -
      2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource chi.toBoundedContinuousFunction

/-- The complete arithmetic quadratic equals its compensated relative form. -/
theorem thetaFullArithmeticQuadratic_eq_relative (chi : 𝓢(ℝ, ℂ)) :
    thetaFullArithmeticQuadratic chi = thetaPrimeGammaPolarRelativeForm chi := by
  rw [thetaFullArithmeticQuadratic, thetaPrimeGammaPolarRelativeForm,
    integral_sub (integrable_thetaGammaPolarQuadraticDensity chi)
      (integrable_thetaGammaPolarDiagonalDensity chi),
    integral_thetaGammaPolarDiagonalDensity_eq_prime]
  ring

/-- Exact ground transform of the full literal prime--Gamma--pole quadratic. -/
theorem thetaFullArithmeticQuadratic_eq_energy_difference (chi : 𝓢(ℝ, ℂ)) :
    thetaFullArithmeticQuadratic chi =
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource chi.toBoundedContinuousFunction -
        thetaGammaPolarScalingEnergy thetaCuspTiltSource chi := by
  rw [thetaFullArithmeticQuadratic_eq_relative, thetaPrimeGammaPolarRelativeForm_eq]

end RHTower.ThetaSourceWard
