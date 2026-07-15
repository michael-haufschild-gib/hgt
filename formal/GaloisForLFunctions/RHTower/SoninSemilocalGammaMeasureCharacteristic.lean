import GaloisForLFunctions.RHTower.SoninSemilocalGammaAutocorrelation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The archimedean Gamma measure and its characteristic function

This module packages the normalized Gamma density from the semilocal Sonin source as an actual
measure.  The autocorrelation computation and Fourier inversion give its characteristic function
exactly: the integral of `exp (i t s)` is `(cosh t)⁻¹ᐟ²`.
-/

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped ENNReal FourierTransform

namespace RHTower

theorem integral_semilocalGammaCharacteristicKernel_normalized (t : ℝ) :
    (((2 * Real.pi) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
        (∫ s : ℝ, semilocalGammaCharacteristicKernel t s) =
      (semilocalArchimedeanCharacteristic t : ℂ) := by
  rw [integral_semilocalGammaCharacteristicKernel_closedForm]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc, semilocalGammaNormalization_constant, one_mul]

/-- The normalized real density
`(2π)⁻³ᐟ² |Γ(1/4 + i s/2)|²` of the archimedean cyclic measure. -/
def semilocalArchimedeanGammaDensity (s : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ) / 2) *
    Complex.normSq
      (Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I))

theorem semilocalArchimedeanGammaDensity_nonneg (s : ℝ) :
    0 ≤ semilocalArchimedeanGammaDensity s := by
  unfold semilocalArchimedeanGammaDensity
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Complex.normSq_nonneg _)

def semilocalArchimedeanGammaDensityNNReal (s : ℝ) : NNReal :=
  ⟨semilocalArchimedeanGammaDensity s,
    semilocalArchimedeanGammaDensity_nonneg s⟩

theorem semilocalArchimedeanGammaDensity_eq_scaledFourier (s : ℝ) :
    (semilocalArchimedeanGammaDensity s : ℂ) =
      ((2 * Real.pi) ^ (-(3 : ℝ) / 2) : ℝ) *
        FourierTransform.fourier semilocalGammaAutocorrelation
          (s / (4 * Real.pi)) := by
  rw [fourier_semilocalGammaAutocorrelation]
  unfold semilocalArchimedeanGammaDensity
  push_cast
  congr 3
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpiC]
  congr 1
  ring

theorem integrable_semilocalArchimedeanGammaDensity :
    Integrable semilocalArchimedeanGammaDensity := by
  have hscaleNe : (4 * Real.pi : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hcomp := integrable_fourier_semilocalGammaAutocorrelation.comp_mul_left' hscaleNe
  have hreal : Integrable (fun s : ℝ =>
      ((2 * Real.pi) ^ (-(3 : ℝ) / 2) : ℝ) *
        (FourierTransform.fourier semilocalGammaAutocorrelation
          ((4 * Real.pi)⁻¹ * s)).re) := by
    exact hcomp.re.const_mul
      ((2 * Real.pi) ^ (-(3 : ℝ) / 2) : ℝ)
  apply hreal.congr
  filter_upwards with s
  have hscaled := semilocalArchimedeanGammaDensity_eq_scaledFourier s
  simpa [div_eq_mul_inv, mul_comm] using (congrArg Complex.re hscaled).symm

theorem continuous_semilocalArchimedeanGammaDensity :
    Continuous semilocalArchimedeanGammaDensity := by
  have hfourier : Continuous
      (FourierTransform.fourier semilocalGammaAutocorrelation) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner integrable_semilocalGammaAutocorrelation
  apply continuous_iff_continuousAt.mpr
  intro s
  have hscaled := semilocalArchimedeanGammaDensity_eq_scaledFourier
  rw [show semilocalArchimedeanGammaDensity = fun y =>
      (Complex.re (((2 * Real.pi) ^ (-(3 : ℝ) / 2) : ℝ) *
        FourierTransform.fourier semilocalGammaAutocorrelation
          (y / (4 * Real.pi)))) by
    funext y
    have h := congrArg Complex.re (hscaled y)
    simpa using h]
  fun_prop

theorem continuous_semilocalArchimedeanGammaDensityNNReal :
    Continuous semilocalArchimedeanGammaDensityNNReal := by
  exact Continuous.subtype_mk continuous_semilocalArchimedeanGammaDensity _

/-- The actual normalized archimedean Gamma measure used by the Sonin semilocal source. -/
def semilocalArchimedeanGammaMeasure : Measure ℝ :=
  volume.withDensity fun s => (semilocalArchimedeanGammaDensityNNReal s : ℝ≥0∞)

theorem integral_cexp_mul_semilocalArchimedeanGammaDensity (t : ℝ) :
    (∫ s : ℝ,
        Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) *
          (semilocalArchimedeanGammaDensity s : ℂ)) =
      (semilocalArchimedeanCharacteristic t : ℂ) := by
  rw [show (fun s : ℝ =>
      Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) *
        (semilocalArchimedeanGammaDensity s : ℂ)) =
      fun s : ℝ =>
        (((2 * Real.pi) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
          semilocalGammaCharacteristicKernel t s by
    funext s
    unfold semilocalArchimedeanGammaDensity semilocalGammaCharacteristicKernel
    push_cast
    ring]
  rw [MeasureTheory.integral_const_mul]
  exact integral_semilocalGammaCharacteristicKernel_normalized t

/-- Equation (6) at degree zero: the characteristic function of the normalized Gamma measure is
exactly `(cosh t)⁻¹ᐟ²`. -/
theorem integral_cexp_semilocalArchimedeanGammaMeasure (t : ℝ) :
    (∫ s : ℝ,
        Complex.exp (((t * s : ℝ) : ℂ) * Complex.I)
          ∂semilocalArchimedeanGammaMeasure) =
      (semilocalArchimedeanCharacteristic t : ℂ) := by
  rw [semilocalArchimedeanGammaMeasure,
    integral_withDensity_eq_integral_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
  rw [show (fun s : ℝ =>
      semilocalArchimedeanGammaDensityNNReal s •
        Complex.exp (((t * s : ℝ) : ℂ) * Complex.I)) =
      fun s : ℝ =>
        Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) *
          (semilocalArchimedeanGammaDensity s : ℂ) by
    funext s
    change (semilocalArchimedeanGammaDensity s : ℂ) *
        Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) = _
    ring]
  exact integral_cexp_mul_semilocalArchimedeanGammaDensity t

end RHTower
