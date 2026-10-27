import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFiniteAmplitudeBounds

/-!
# Uniform finite theta bounds on vertical strips

The modulus of each bilateral theta integrand depends only on the real
part of the spectral parameter. The integer Gaussian tail therefore
controls the amplitudes uniformly at every ordinate in a fixed strip.
-/

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

lemma theta_amplitude_integrand_strip_bound {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : |z.re| ≤ R) (x : ℝ) :
    thetaCuspFullSource x * ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) := by
  have he : ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ =
      ‖Complex.exp (((1 / 2 : ℂ) - (z.re : ℂ)) * (x : ℂ))‖ := by
    simp [Complex.norm_exp]
  rw [he]
  exact theta_amplitude_integrand_bound hR (by simpa using hz) x

private lemma norm_theta_dominated_integral_le_strip (F : ℝ → ℂ)
    (hF : Integrable F) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) {z : ℂ}
    (hz : |z.re| ≤ R)
    (hb : ∀ x, ‖F x‖ ≤ C * (thetaCuspFullSource x *
      ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖)) :
    ‖∫ x : ℝ, F x‖ ≤ C * thetaAmplitudeEnvelope R := by
  calc
    ‖∫ x : ℝ, F x‖ ≤ ∫ x : ℝ, ‖F x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, C * (thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|)) := by
      apply integral_mono_ae hF.norm ((integrable_thetaAmplitudeProfile.const_mul _).const_mul _)
      filter_upwards with x
      exact (hb x).trans (mul_le_mul_of_nonneg_left
        (theta_amplitude_integrand_strip_bound hR hz x) hC)
    _ = _ := by rw [integral_const_mul, integral_const_mul]; rfl

/-- The full theta amplitude has a bound independent of ordinate in every fixed strip. -/
theorem norm_fullThetaAmplitude_le_strip {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : |z.re| ≤ R) :
    ‖bilateralLaplace thetaCuspTiltSource ((1 / 2 : ℂ) - z)‖ ≤ thetaAmplitudeEnvelope R := by
  have h := norm_theta_dominated_integral_le_strip
    (fun x => (thetaCuspTiltSource.k x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))
    (integrable_bilateralLaplace thetaCuspTiltSource _) (C := 1) (by norm_num) hR hz
    (fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaCuspTiltSource.pos x), one_mul]
      rw [thetaCuspTiltSource_k])
  simpa only [bilateralLaplace, one_mul] using h

/-- Every nonempty literal prefix inherits the same vertical-strip envelope. -/
theorem norm_finiteThetaAmplitude_le_strip (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : |z.re| ≤ R) : ‖finiteThetaAmplitude N z‖ ≤ thetaAmplitudeEnvelope R := by
  rw [finiteThetaAmplitude_eq_bilateral]
  have h := norm_theta_dominated_integral_le_strip
    (fun x => ((finiteThetaTiltSource N).k x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))
    (integrable_bilateralLaplace (finiteThetaTiltSource N) _) (C := 1) (by norm_num) hR hz
    (fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ((finiteThetaTiltSource N).pos x), one_mul]
      exact mul_le_mul_of_nonneg_right (reflectedFiniteThetaSource_le_full (N + 1) x)
        (norm_nonneg _))
  simpa only [bilateralLaplace, one_mul] using h

/-- Integer truncation has a Gaussian error uniform along the entire vertical strip. -/
theorem norm_finiteThetaAmplitude_sub_full_le_strip (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : |z.re| ≤ R) :
    ‖finiteThetaAmplitude N z - bilateralLaplace thetaCuspTiltSource ((1 / 2 : ℂ) - z)‖ ≤
      thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) *
        thetaAmplitudeEnvelope R := by
  have hN := integrable_bilateralLaplace (finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hfull := integrable_bilateralLaplace thetaCuspTiltSource ((1 / 2 : ℂ) - z)
  rw [finiteThetaAmplitude_eq_bilateral, bilateralLaplace, bilateralLaplace,
    ← integral_sub hN hfull]
  apply norm_theta_dominated_integral_le_strip _ (hN.sub hfull)
    (mul_nonneg thetaCuspIntegerTailConstant_nonneg (Real.exp_pos _).le) hR hz
  intro x
  dsimp only [Pi.sub_apply]
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_sub_comm]
  have htail := (reflectedFiniteThetaSource_relative_tail (N + 1) x).2
  calc
    |thetaCuspTiltSource.k x - (finiteThetaTiltSource N).k x| *
        ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      ((thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) *
        thetaCuspFullSource x) * ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ :=
      mul_le_mul_of_nonneg_right htail (norm_nonneg _)
    _ = _ := by ring

end RHTower

#print axioms RHTower.norm_fullThetaAmplitude_le_strip
#print axioms RHTower.norm_finiteThetaAmplitude_sub_full_le_strip
