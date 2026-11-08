import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanSchwartz
import GaloisForLFunctions.HTGeometry.NyquistLatticeSum

/-!
# Literal Narain spectral and physical Schwartz functions

Frequency dilation and reflection identify the actual Mellin boundary
and normalized physical remainder. Their polynomial moments converge
absolutely; the central Mellin zero forces a vanishing clock integral.
-/

open Complex RHTower MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The literal unscaled imaginary-axis Mellin boundary as a Schwartz function. -/
def narainMeanSpectralSchwartz (Y Z : Height) : SchwartzMap ℝ ℂ :=
  schwartzScale (narainMeanBoundarySchwartz Y Z)
    (c := (2 * Real.pi)⁻¹) (inv_ne_zero (by positivity))

/-- Frequency dilation recovers the actual Mellin boundary without a reparametrization. -/
theorem narainMeanSpectralSchwartz_apply (Y Z : Height) (t : ℝ) :
    narainMeanSpectralSchwartz Y Z t = narainMellinMean Y Z ((t : ℂ) * I) := by
  rw [narainMeanSpectralSchwartz, schwartzScale_apply, narainMeanBoundarySchwartz_apply,
    narainMeanBoundaryFrequency]
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The reflected Fourier profile is the normalized actual source on its logarithmic clock. -/
def narainMeanClockSchwartz (Y Z : Height) : SchwartzMap ℝ ℂ :=
  schwartzScale (narainMeanFourierSchwartz Y Z) (c := -1) (by norm_num)

/-- The Schwartz clock is exactly the physical remainder, including both main terms. -/
theorem narainMeanClockSchwartz_apply (Y Z : Height) (L : ℝ) :
    narainMeanClockSchwartz Y Z L = (Real.exp (L / 2) : ℂ) *
      ((Real.exp (-L) : ℂ) * narainScalarHeatAverage Y Z (Real.exp (-L)) -
        (3 / (Real.pi : ℂ)) * (L : ℂ) - narainAverageConstant Y Z) := by
  rw [narainMeanClockSchwartz, schwartzScale_apply, neg_one_mul, narainMeanFourierSchwartz_apply]
  have hs := narainScalarHeatAverage_remainder_eq_fourier Y Z (Real.exp_pos (-L))
  simp only [Real.log_exp, Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg] at hs
  have hy : (Real.exp (-L) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hcancel : (Real.exp (L / 2) : ℂ) *
      (Real.exp (-L) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hy, ← Complex.ofReal_log (Real.exp_pos (-L)).le,
      Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
    rw [show ((L / 2 : ℝ) : ℂ) + ((-L : ℝ) : ℂ) * (1 / 2 : ℂ) = 0 by push_cast; ring,
      Complex.exp_zero]
  rw [hs, ← mul_assoc, hcancel, one_mul]

/-- The universal central zero forces the zeroth moment of the actual clock remainder to vanish. -/
theorem integral_narainMeanClockSchwartz (Y Z : Height) :
    ∫ L : ℝ, narainMeanClockSchwartz Y Z L = 0 := by
  have h := narainMeanBoundarySchwartz_apply Y Z 0
  change ((FourierTransform.fourierInv (narainMeanFourierSchwartz Y Z) : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0 =
    narainMeanBoundaryFrequency Y Z 0 at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero,
    fourier_zero_eq_integral] at h
  simp only [narainMeanBoundaryFrequency, Complex.ofReal_zero, mul_zero, zero_mul, narainMellinMean_zero] at h
  have heq : (fun L : ℝ => narainMeanClockSchwartz Y Z L) =
      fun L : ℝ => narainMeanFourierSchwartz Y Z (-L) := by
    funext L
    rw [narainMeanClockSchwartz, schwartzScale_apply, neg_one_mul]
  rw [heq, integral_neg_eq_self]
  exact h

/-- The literal physical clock moment is absolutely integrable. -/
theorem integrable_narainMeanClockSource (Y Z : Height) :
    Integrable (fun L : ℝ => (Real.exp (L / 2) : ℂ) *
      ((Real.exp (-L) : ℂ) * narainScalarHeatAverage Y Z (Real.exp (-L)) -
        (3 / (Real.pi : ℂ)) * (L : ℂ) - narainAverageConstant Y Z)) := by
  have hf : (narainMeanClockSchwartz Y Z : ℝ → ℂ) =
      fun L : ℝ => (Real.exp (L / 2) : ℂ) *
        ((Real.exp (-L) : ℂ) * narainScalarHeatAverage Y Z (Real.exp (-L)) -
          (3 / (Real.pi : ℂ)) * (L : ℂ) - narainAverageConstant Y Z) :=
    funext (narainMeanClockSchwartz_apply Y Z)
  rw [← hf]
  exact (narainMeanClockSchwartz Y Z).integrable (μ := (volume : Measure ℝ))

/-- Every polynomial clock moment of the literal physical remainder converges absolutely. -/
theorem integrable_narainMeanClockSource_moment (Y Z : Height) (n : ℕ) :
    Integrable (fun L : ℝ => ‖L‖ ^ n * ‖(Real.exp (L / 2) : ℂ) *
      ((Real.exp (-L) : ℂ) * narainScalarHeatAverage Y Z (Real.exp (-L)) -
        (3 / (Real.pi : ℂ)) * (L : ℂ) - narainAverageConstant Y Z)‖) := by
  simpa only [narainMeanClockSchwartz_apply] using
    (narainMeanClockSchwartz Y Z).integrable_pow_mul volume n

/-- Every derivative of the literal spectral boundary has all absolute polynomial moments. -/
theorem integrable_narainMeanSpectral_derivative_moment (Y Z : Height) (k n : ℕ) :
    Integrable (fun t : ℝ => ‖t‖ ^ k *
      ‖iteratedDeriv n (fun v : ℝ => narainMellinMean Y Z ((v : ℂ) * I)) t‖) := by
  have hf : (narainMeanSpectralSchwartz Y Z : ℝ → ℂ) =
      fun v : ℝ => narainMellinMean Y Z ((v : ℂ) * I) :=
    funext (narainMeanSpectralSchwartz_apply Y Z)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hf] using
    (narainMeanSpectralSchwartz Y Z).integrable_pow_mul_iteratedFDeriv volume k n

/-- The physical remainder has an exact vanishing logarithmic-clock moment. -/
theorem integral_narainMeanClockSource (Y Z : Height) :
    (∫ L : ℝ, (Real.exp (L / 2) : ℂ) *
      ((Real.exp (-L) : ℂ) * narainScalarHeatAverage Y Z (Real.exp (-L)) -
        (3 / (Real.pi : ℂ)) * (L : ℂ) - narainAverageConstant Y Z)) = 0 := by
  simpa only [narainMeanClockSchwartz_apply] using integral_narainMeanClockSchwartz Y Z

#print axioms narainMeanSpectralSchwartz_apply
#print axioms narainMeanClockSchwartz_apply
#print axioms integrable_narainMeanClockSource_moment
#print axioms integrable_narainMeanSpectral_derivative_moment
#print axioms integral_narainMeanClockSource
#print axioms integrable_narainMeanClockSource
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
