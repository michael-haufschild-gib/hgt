import GaloisForLFunctions.HTGeometry.GaussianMellinMoments

/-!
# Gaussian Kummer probes

The Gaussian probe of width `μ` is the heat vector `g_μ(x) = e^{-π μ² x²}` of the Kummer phase
generator: on the character of frequency `ℓ(a)` the heat operator `e^{-π x² D²}` acts by
`g_{|ℓ(a)|}(x)`.  Its Fourier transform inverts the width and divides by it, its Mellin transform
is the completed Gamma factor divided by the width to the power of the variable, and rescaling the
width is the same as rescaling the argument, so the Kummer power orbit is the dilation orbit.

* `deningerGaussianProbe` : the probe `(1)`.
* `deningerGaussianProbe_heat` : the heat-vector identity `(4)`.
* `deningerGaussianProbe_fourier` : the Fourier identity `(2)`.
* `deningerGaussianProbe_mellin` : the Mellin identity `(3)`.
* `deningerGaussianProbe_dilation` : the power orbit `(8)`.
-/

namespace RHTower

open Complex MeasureTheory Set
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

section GaussianProbe

/-- The Gaussian probe of width `μ`. -/
noncomputable def deningerGaussianProbe (μ : ℝ) (x : ℝ) : ℂ :=
  gaussianKernel (μ * x)

theorem deningerGaussianProbe_apply (μ x : ℝ) :
    deningerGaussianProbe μ x = ((Real.exp (-Real.pi * (μ * x) ^ 2) : ℝ) : ℂ) := rfl

theorem deningerGaussianProbe_zero (μ : ℝ) : deningerGaussianProbe μ 0 = 1 := by
  rw [deningerGaussianProbe_apply]
  norm_num

/-- The probe as a complex exponential. -/
theorem deningerGaussianProbe_cexp (μ x : ℝ) :
    deningerGaussianProbe μ x = Complex.exp (-(Real.pi : ℂ) * ((μ : ℂ) ^ 2) * (x : ℂ) ^ 2) := by
  rw [deningerGaussianProbe_apply, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **The heat-vector identity.**  On a character of frequency `m` the Gaussian heat operator of
the phase generator acts by the probe of width `|m|`. -/
theorem deningerGaussianProbe_heat (m x : ℝ) :
    ((Real.exp (-Real.pi * x ^ 2 * m ^ 2) : ℝ) : ℂ) = deningerGaussianProbe |m| x := by
  rw [deningerGaussianProbe_apply]
  congr 2
  rw [mul_pow, sq_abs]
  ring

/-- **The power orbit is the dilation orbit.**  Scaling the width is scaling the argument. -/
theorem deningerGaussianProbe_dilation (n μ x : ℝ) :
    deningerGaussianProbe (n * μ) x = deningerGaussianProbe μ (n * x) := by
  rw [deningerGaussianProbe, deningerGaussianProbe]
  congr 1
  ring

/-- The half power of the squared width is the width. -/
theorem deningerWidth_cpow_half {μ : ℝ} (hμ : 0 < μ) :
    ((μ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (μ : ℂ) := by
  have hcast : ((μ : ℂ) ^ 2) = (((μ ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  have hhalf : ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, hhalf, ← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [← Real.rpow_natCast μ 2, ← Real.rpow_mul (le_of_lt hμ)]
  norm_num

/-- **The Fourier identity.**  The probe of width `μ` has Fourier transform the probe of the
inverse width, divided by the width. -/
theorem deningerGaussianProbe_fourier {μ : ℝ} (hμ : 0 < μ) :
    (𝓕 (deningerGaussianProbe μ)) = fun y : ℝ => (μ : ℂ)⁻¹ * deningerGaussianProbe μ⁻¹ y := by
  have hb : (0 : ℝ) < ((μ : ℂ) ^ 2).re := by
    have : ((μ : ℂ) ^ 2).re = μ ^ 2 := by
      simp [pow_two, Complex.mul_re]
    rw [this]
    positivity
  have hfun : deningerGaussianProbe μ
      = fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * ((μ : ℂ) ^ 2) * (x : ℂ) ^ 2) :=
    funext (deningerGaussianProbe_cexp μ)
  rw [hfun, fourier_gaussian_pi hb]
  funext y
  rw [deningerWidth_cpow_half hμ, deningerGaussianProbe_cexp]
  have hinv : ((μ⁻¹ : ℝ) : ℂ) = ((μ : ℂ))⁻¹ := by push_cast; ring
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hμ
  rw [hinv, one_div]
  congr 2
  field_simp

/-- **The Mellin identity.**  The Mellin transform of the probe is half the completed Gamma factor
divided by the width to the power of the variable. -/
theorem deningerGaussianProbe_mellin {μ : ℝ} (hμ : 0 < μ) {s : ℂ} (hs : 0 < s.re) :
    mellin (deningerGaussianProbe μ) s = (μ : ℂ) ^ (-s) * (Complex.Gammaℝ s / 2) := by
  have h := mellin_comp_mul_left gaussianKernel s hμ
  rw [mellin_gaussianKernel hs] at h
  have hfun : deningerGaussianProbe μ = fun t : ℝ => gaussianKernel (μ * t) := rfl
  rw [hfun, h, smul_eq_mul]

end GaussianProbe

end RHTower
