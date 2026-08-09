import Mathlib.Analysis.Fourier.Inversion

/-!
# Scaled Fourier inversion for corpus-normalized frequency integrals

Corpus-normalized frequency integrals carry the kernel `e^{-itξ₀}` against a transform evaluated
at `t/(2π)`.  Rescaling and inverting: for continuous `h` with `h` and `𝓕 h` integrable,

`∫ t, e^{-itξ₀}·𝓕h(t/(2π)) dt = 2π·h(-ξ₀)`.

This converts each single-frequency line integral of the termwise von Mangoldt swap into a
time-side sample of the underlying convolution.
-/

namespace HTGeometry

noncomputable section

open MeasureTheory Complex FourierTransform

/-- **Scaled Fourier inversion.**  For continuous `h` with `h` and `𝓕 h` integrable, the
corpus-normalized frequency integral of `𝓕 h` against `e^{-itξ₀}` returns `2π·h(-ξ₀)`. -/
theorem integral_exp_mul_fourier_scaled {h : ℝ → ℂ}
    (hcont : Continuous h) (hh : Integrable h) (hFh : Integrable (𝓕 h)) (ξ₀ : ℝ) :
    (∫ t : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (ξ₀ : ℂ)) * 𝓕 h (t / (2 * Real.pi)))
      = 2 * Real.pi * h (-ξ₀) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsub := Measure.integral_comp_inv_mul_right
    (fun s : ℝ =>
      Complex.exp (-Complex.I * ((2 * Real.pi * s : ℝ) : ℂ) * (ξ₀ : ℂ)) * 𝓕 h s)
    (2 * Real.pi)
  have hlhs :
      (∫ t : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (ξ₀ : ℂ)) * 𝓕 h (t / (2 * Real.pi)))
        = ∫ t : ℝ,
            Complex.exp (-Complex.I * ((2 * Real.pi * (t * (2 * Real.pi)⁻¹) : ℝ) : ℂ) * (ξ₀ : ℂ)) *
              𝓕 h (t * (2 * Real.pi)⁻¹) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : (2 * Real.pi * (t * (2 * Real.pi)⁻¹) : ℝ) = t := by
      field_simp
    have h2 : (t / (2 * Real.pi) : ℝ) = t * (2 * Real.pi)⁻¹ := div_eq_mul_inv t _
    show Complex.exp (-Complex.I * (t : ℂ) * (ξ₀ : ℂ)) * 𝓕 h (t / (2 * Real.pi)) =
      Complex.exp (-Complex.I * ((2 * Real.pi * (t * (2 * Real.pi)⁻¹) : ℝ) : ℂ) * (ξ₀ : ℂ)) *
        𝓕 h (t * (2 * Real.pi)⁻¹)
    rw [h1, h2]
  have hfour :
      (∫ s : ℝ,
          Complex.exp (-Complex.I * ((2 * Real.pi * s : ℝ) : ℂ) * (ξ₀ : ℂ)) * 𝓕 h s)
        = 𝓕 (𝓕 h) ξ₀ := by
    rw [Real.fourier_real_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show Complex.exp (-Complex.I * ((2 * Real.pi * s : ℝ) : ℂ) * (ξ₀ : ℂ)) * 𝓕 h s =
      (Real.fourierChar (-(s * ξ₀)) : ℂ) • 𝓕 h s
    rw [Real.fourierChar_apply, smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hinv : 𝓕 (𝓕 h) ξ₀ = h (-ξ₀) := by
    have h1 : 𝓕⁻ (𝓕 h) (-ξ₀) = 𝓕 (𝓕 h) (- -ξ₀) :=
      Real.fourierInv_eq_fourier_neg (𝓕 h) (-ξ₀)
    have h2 := hcont.fourierInv_fourier_eq hh hFh
    have h3 : 𝓕⁻ (𝓕 h) (-ξ₀) = h (-ξ₀) := by rw [h2]
    rw [neg_neg] at h1
    rw [← h1, h3]
  rw [hlhs, hsub, hfour, hinv]
  rw [abs_of_pos hπ]
  simp

end

end HTGeometry
