import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedFiniteSource

/-!
# Disc bounds for literal finite theta amplitudes

The completed theta source dominates every reflected finite prefix.
Its global exponential envelope bounds their bilateral amplitudes and
converts the relative integer tail into a uniform complex-disc estimate.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- Fixed mass of the exponential comparison profile. -/
def thetaAmplitudeProfileMass : ℝ := ∫ x : ℝ, Real.exp (-|x|)

lemma integrable_thetaAmplitudeProfile : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  simpa only [pow_zero, one_mul, neg_one_mul] using
    HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 one_pos

lemma thetaAmplitudeProfileMass_nonneg : 0 ≤ thetaAmplitudeProfileMass :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- An arithmetic amplitude bound on a spectral disc. -/
def thetaAmplitudeEnvelope (R : ℝ) : ℝ :=
  thetaCuspTiltDecayConstant (R + 5 / 2) * thetaAmplitudeProfileMass

lemma thetaAmplitudeEnvelope_nonneg (R : ℝ) : 0 ≤ thetaAmplitudeEnvelope R :=
  mul_nonneg (thetaCuspTiltDecayConstant_pos _).le thetaAmplitudeProfileMass_nonneg

lemma theta_amplitude_integrand_bound {R : ℝ} (_hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R)
    (x : ℝ) :
    thetaCuspFullSource x * ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) := by
  have hre : (1 / 2 - z.re) * x ≤ (R + 1 / 2) * |x| := by
    have hzre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hz
    have h : |1 / 2 - z.re| ≤ R + 1 / 2 := by
      have ha := abs_sub (1 / 2 : ℝ) z.re
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at ha
      linarith only [ha, hzre]
    calc
      (1 / 2 - z.re) * x ≤ |(1 / 2 - z.re) * x| := le_abs_self _
      _ = |1 / 2 - z.re| * |x| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right h (abs_nonneg _)
  have hexp : ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      Real.exp ((R + 1 / 2) * |x|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
    simpa only [he] using hre
  calc
    thetaCuspFullSource x * ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
        (thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-((R + 5 / 2) * |x|))) *
          Real.exp ((R + 1 / 2) * |x|) :=
      mul_le_mul (thetaCuspFullSource_le_tiltDecayConstant (R + 5 / 2) x) hexp
        (norm_nonneg _)
        (mul_nonneg (thetaCuspTiltDecayConstant_pos _).le (Real.exp_pos _).le)
    _ = thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-2 * |x|) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith only [abs_nonneg x]))
      (thetaCuspTiltDecayConstant_pos _).le

/-- The complete arithmetic amplitude has the same explicit envelope as every finite prefix. -/
theorem norm_fullThetaAmplitude_le {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖bilateralLaplace thetaCuspTiltSource ((1 / 2 : ℂ) - z)‖ ≤ thetaAmplitudeEnvelope R := by
  unfold bilateralLaplace
  calc
    ‖∫ x : ℝ, (thetaCuspTiltSource.k x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      ∫ x : ℝ, ‖(thetaCuspTiltSource.k x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) := by
      apply integral_mono_ae (integrable_bilateralLaplace thetaCuspTiltSource _).norm
        (integrable_thetaAmplitudeProfile.const_mul _)
      filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaCuspTiltSource.pos x)]
      exact theta_amplitude_integrand_bound hR hz x
    _ = thetaAmplitudeEnvelope R := by rw [integral_const_mul]; rfl

/-- Integer prefixes inherit the full amplitude envelope without a bound on their derivatives. -/
theorem norm_finiteThetaAmplitude_le (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) : ‖finiteThetaAmplitude N z‖ ≤ thetaAmplitudeEnvelope R := by
  rw [finiteThetaAmplitude_eq_bilateral]
  unfold bilateralLaplace
  calc
    ‖∫ x : ℝ, ((finiteThetaTiltSource N).k x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      ∫ x : ℝ, ‖((finiteThetaTiltSource N).k x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) := by
      apply integral_mono_ae (integrable_bilateralLaplace (finiteThetaTiltSource N) _).norm
        (integrable_thetaAmplitudeProfile.const_mul _)
      filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ((finiteThetaTiltSource N).pos x)]
      exact (mul_le_mul_of_nonneg_right (reflectedFiniteThetaSource_le_full (N + 1) x)
        (norm_nonneg _)).trans (theta_amplitude_integrand_bound hR hz x)
    _ = thetaAmplitudeEnvelope R := by rw [integral_const_mul]; rfl

/-- The literal finite amplitude converges on every disc with a Gaussian integer-tail error. -/
theorem norm_finiteThetaAmplitude_sub_full_le (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖finiteThetaAmplitude N z - bilateralLaplace thetaCuspTiltSource ((1 / 2 : ℂ) - z)‖ ≤
      thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) *
        thetaAmplitudeEnvelope R := by
  have hN := integrable_bilateralLaplace (finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hfull := integrable_bilateralLaplace thetaCuspTiltSource ((1 / 2 : ℂ) - z)
  rw [finiteThetaAmplitude_eq_bilateral, bilateralLaplace, bilateralLaplace,
    ← integral_sub hN hfull]
  calc
    ‖∫ x : ℝ, ((finiteThetaTiltSource N).k x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
      (thetaCuspTiltSource.k x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      ∫ x : ℝ, ‖((finiteThetaTiltSource N).k x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
      (thetaCuspTiltSource.k x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) *
        (thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|)) := by
      apply integral_mono_ae (hN.sub hfull).norm
        ((integrable_thetaAmplitudeProfile.const_mul _).const_mul _)
      filter_upwards with x
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
        _ = (thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) *
            (thetaCuspFullSource x * ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (theta_amplitude_integrand_bound hR hz x)
          (mul_nonneg thetaCuspIntegerTailConstant_nonneg (Real.exp_pos _).le)
    _ = _ := by rw [integral_const_mul, integral_const_mul]; rfl

end RHTower

#print axioms RHTower.norm_finiteThetaAmplitude_sub_full_le
