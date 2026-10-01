import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform


open MeasureTheory Complex
noncomputable section
namespace RHTower

/-- The normalized logarithmic Gaussian whose upper tail is the actual smoothing cutoff. -/
def smoothAFELogGaussian (y : ℝ) : ℝ := Real.exp (-y ^ 2 / 4) / (2 * Real.sqrt Real.pi)

private theorem logGaussian_mul_exp_eq (s : ℂ) (y : ℝ) :
    (smoothAFELogGaussian y : ℂ) * Complex.exp (s * y) =
      Complex.exp ((-(1 / 4 : ℂ)) * (y : ℂ) ^ 2 + s * y + 0) /
        (2 * (Real.sqrt Real.pi : ℂ)) := by
  unfold smoothAFELogGaussian
  rw [Complex.ofReal_div, Complex.ofReal_exp, div_mul_eq_mul_div, ← Complex.exp_add]
  push_cast
  congr 2
  ring

/-- Every complex exponential tilt of the actual logarithmic Gaussian is integrable. -/
theorem integrable_smoothAFELogGaussian_mul_exp (s : ℂ) :
    Integrable (fun y : ℝ => (smoothAFELogGaussian y : ℂ) * Complex.exp (s * y)) := by
  simp_rw [logGaussian_mul_exp_eq]
  exact (integrable_cexp_quadratic' (by norm_num : (-(1 / 4 : ℂ)).re < 0) s 0).div_const _

/-- The exact Gaussian exponential moment supplies the entire numerator in the Mellin response. -/
theorem integral_smoothAFELogGaussian_mul_exp (s : ℂ) :
    (∫ y : ℝ, (smoothAFELogGaussian y : ℂ) * Complex.exp (s * y)) = Complex.exp (s ^ 2) := by
  simp_rw [logGaussian_mul_exp_eq]
  rw [integral_div, integral_cexp_quadratic (by norm_num : (-(1 / 4 : ℂ)).re < 0) s 0]
  have hroot : ((Real.pi : ℂ) / -(-(1 / 4 : ℂ))) ^ (1 / 2 : ℂ) =
      2 * (Real.sqrt Real.pi : ℂ) := by
    rw [show (Real.pi : ℂ) / -(-(1 / 4 : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 4 * Real.pi) (1 / 2 : ℝ),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [hfour]
  rw [hroot, show (0 : ℂ) - s ^ 2 / (4 * -(1 / 4 : ℂ)) = s ^ 2 by ring]
  have hden : (2 * (Real.sqrt Real.pi : ℂ)) ≠ 0 := by
    have hpos := Real.sqrt_pos.mpr Real.pi_pos
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hpos.ne')
  field_simp

/-- Gaussian domination remains integrable after every real exponential weight. -/
theorem integrable_smoothAFELogGaussian_mul_real_exp (σ : ℝ) :
    Integrable (fun y : ℝ => smoothAFELogGaussian y * Real.exp (σ * y)) := by
  have h := (integrable_smoothAFELogGaussian_mul_exp (σ : ℂ)).re
  apply h.congr
  filter_upwards with y
  change ((smoothAFELogGaussian y : ℂ) * Complex.exp ((σ : ℂ) * y)).re =
    smoothAFELogGaussian y * Real.exp (σ * y)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

end RHTower
