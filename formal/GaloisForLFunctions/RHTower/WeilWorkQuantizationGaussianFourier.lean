import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The scalar kernel for actual Gaussian coefficient recovery

This is the classical Gaussian Fourier integral on the line with real
part one. Its exact normalization cancels the apparent exponential tilt
when the centered Dirichlet series is extracted on its absolute line.
-/

open Complex MeasureTheory
noncomputable section
namespace RHTower.WeilSpectral

def quantizationGaussianFourierKernel (T x t : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * (1 + t * I) + (1 + t * I) ^ 2 / T ^ 2)

private theorem kernel_quadratic {T : ℝ} (hT : 0 < T) (x t : ℝ) :
    (x : ℂ) * (1 + t * I) + (1 + t * I) ^ 2 / T ^ 2 =
      -(1 / (T : ℂ) ^ 2) * t ^ 2 + ((x + 2 / T ^ 2) * I) * t + (x + 1 / T ^ 2) := by
  have hTc : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem integrable_quantizationGaussianFourierKernel {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Integrable (quantizationGaussianFourierKernel T x) := by
  have hb : 0 < (1 / (T : ℂ) ^ 2).re := by
    have he : (1 / (T : ℂ) ^ 2).re = 1 / T ^ 2 := by norm_cast
    rw [he]
    positivity
  change Integrable (fun t : ℝ => Complex.exp
    ((x : ℂ) * (1 + t * I) + (1 + t * I) ^ 2 / T ^ 2))
  simpa only [kernel_quadratic hT] using
    integrable_cexp_quadratic hb (((x : ℂ) + 2 / T ^ 2) * I) ((x : ℂ) + 1 / T ^ 2)

theorem integral_quantizationGaussianFourierKernel {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (∫ t : ℝ, quantizationGaussianFourierKernel T x t) =
      ((T * Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-((T * x) ^ 2 / 4 : ℝ)) := by
  have hTc : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
  have hb : (-(1 / (T : ℂ) ^ 2)).re < 0 := by
    have he : (-(1 / (T : ℂ) ^ 2)).re = -(1 / T ^ 2) := by norm_cast
    rw [he]
    exact neg_lt_zero.mpr (by positivity)
  simp_rw [quantizationGaussianFourierKernel, kernel_quadratic hT]
  rw [integral_cexp_quadratic hb]
  have hbase : (Real.pi : ℂ) / -(-(1 / (T : ℂ) ^ 2)) = ((Real.pi * T ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hsqrt : (((Real.pi * T ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      ((T * Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hT.le]
    push_cast
    ring
  rw [hbase, hsqrt]
  congr 2
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end RHTower.WeilSpectral
