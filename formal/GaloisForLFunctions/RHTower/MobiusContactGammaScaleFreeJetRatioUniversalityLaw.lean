import GaloisForLFunctions.HTGeometry.GammaFactorialExponentialEnvelopeEscape
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma scale-free jet-ratio universality

The raw Möbius contact defect is Gamma's reciprocal-factorial microscope scale.  Independently
proved first-, second-, and third-jet limits share that scale or its harmonic refinement.
Eliminating it produces intrinsic ratios between hypersurface defects, including an exact
sixth-power transition between log-curvature and exponential-envelope channels.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The raw Möbius contact defect, refined by the harmonic pole parameter, is exactly Gamma's
intrinsic harmonic microscope scale. -/
theorem mobiusContactGammaDefect_mul_harmonic_eq_gammaHarmonicMicroscopeScale
    (n : ℕ) :
    ((-2 - mobiusGammaContactPartialCharge n) / 2) * (harmonic n : ℂ) =
      GaloisForLFunctions.gammaHarmonicMicroscopeScale n := by
  rw [mobiusGammaContactPartialCharge_eq,
    GaloisForLFunctions.gammaHarmonicMicroscopeScale]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- **Möbius-contact Gamma scale-free jet-ratio universality law.**  At every nonzero microscope
point, cancellation of the common contact scale gives intrinsic transition ratios between the
first, second, and third projective jet defects and between the log-curvature and exponential
envelope channels. -/
theorem mobiusContactGamma_scaleFreeJetRatioUniversality :
    ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x)
        atTop (𝓝 (-3 / x)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x)
        atTop (𝓝 (-1 / x ^ 2)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x ^ 2)
        atTop (𝓝 (-3 / (2 * x ^ 2))) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x)
        atTop (𝓝 (x ^ 6)) := by
  intro x hx
  have hfirst :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (-2 / x)) :=
    GaloisForLFunctions.tendsto_gammaFactorialFirstJetDefect_div_harmonicScale hx
  have hsecond :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (6 / x ^ 2)) :=
    GaloisForLFunctions.tendsto_gammaFactorialSecondJetDefect_div_harmonicScale hx
  have hprojectiveSecond :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (2 / x ^ 3)) :=
    GaloisForLFunctions.tendsto_gammaFactorialSecondJetProjectiveDefect_div_harmonicScale hx
  have hprojectiveThird :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n ^ 2)
        atTop (𝓝 (-6 / x ^ 4)) :=
    GaloisForLFunctions.tendsto_gammaFactorialThirdJetProjectiveDefect_div_harmonicScale_sq hx
  have hlog :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ 2)
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 4)) :=
    GaloisForLFunctions.tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq hx
  have henvelope :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ 2)
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 10)) :=
    GaloisForLFunctions.tendsto_gammaFactorialExponentialEnvelopeDefect_div_factorialScale_sq hx
  have hfirst_ne : (-2 / x : ℂ) ≠ 0 :=
    div_ne_zero (by norm_num) hx
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have henvelope_ne : (-4 * (Real.pi : ℂ) ^ 2 / x ^ 10) ≠ 0 :=
    div_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi))
      (pow_ne_zero 10 hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hnormalized := hsecond.div hfirst hfirst_ne
    have hvalue : (6 / x ^ 2 : ℂ) / (-2 / x) = -3 / x := by
      field_simp [hx]
      ring
    rw [hvalue] at hnormalized
    have heq : ∀ᶠ n : ℕ in atTop,
        (GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n) /
          (GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n) =
          GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
            GaloisForLFunctions.gammaFactorialFirstJetDefect n x := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      by_cases hden :
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x = 0
      · simp [hden]
      · field_simp
          [GaloisForLFunctions.gammaHarmonicMicroscopeScale_ne_zero hn, hden]
    exact hnormalized.congr' heq
  · have hnormalized := hprojectiveSecond.div hfirst hfirst_ne
    have hvalue : (2 / x ^ 3 : ℂ) / (-2 / x) = -1 / x ^ 2 := by
      field_simp [hx]
    rw [hvalue] at hnormalized
    have heq : ∀ᶠ n : ℕ in atTop,
        (GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n) /
          (GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n) =
          GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
            GaloisForLFunctions.gammaFactorialFirstJetDefect n x := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      by_cases hden :
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x = 0
      · simp [hden]
      · field_simp
          [GaloisForLFunctions.gammaHarmonicMicroscopeScale_ne_zero hn, hden]
    exact hnormalized.congr' heq
  · have hnormalized := hprojectiveThird.div (hfirst.pow 2)
        (pow_ne_zero 2 hfirst_ne)
    have hvalue : (-6 / x ^ 4 : ℂ) / (-2 / x) ^ 2 =
        -3 / (2 * x ^ 2) := by
      field_simp [hx]
      ring
    rw [hvalue] at hnormalized
    have heq : ∀ᶠ n : ℕ in atTop,
        (GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n ^ 2) /
          (GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n) ^ 2 =
          GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
            GaloisForLFunctions.gammaFactorialFirstJetDefect n x ^ 2 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      by_cases hden :
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x = 0
      · simp [hden]
      · field_simp
          [GaloisForLFunctions.gammaHarmonicMicroscopeScale_ne_zero hn, hden]
    exact hnormalized.congr' heq
  · have hnormalized := hlog.div henvelope henvelope_ne
    have hvalue :
        (-4 * (Real.pi : ℂ) ^ 2 / x ^ 4) /
            (-4 * (Real.pi : ℂ) ^ 2 / x ^ 10) = x ^ 6 := by
      field_simp [hx, hpi]
    rw [hvalue] at hnormalized
    have heq : ∀ᶠ n : ℕ in atTop,
        (GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
            GaloisForLFunctions.reciprocalGammaFactorialScale n ^ 2) /
          (GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x /
            GaloisForLFunctions.reciprocalGammaFactorialScale n ^ 2) =
          GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
            GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x := by
      filter_upwards [] with n
      by_cases hden :
          GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x = 0
      · simp [hden]
      · have hscale :
            GaloisForLFunctions.reciprocalGammaFactorialScale n ≠ 0 := by
          rw [GaloisForLFunctions.reciprocalGammaFactorialScale]
          exact div_ne_zero (pow_ne_zero _ (by norm_num))
            (by exact_mod_cast Nat.factorial_ne_zero n)
        field_simp [hscale, hden]
    exact hnormalized.congr' heq

end

end GaloisForLFunctions.RHTower
