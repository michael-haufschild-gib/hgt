/-
# Chen--Gupta--Li `h_t`: first Fourier integration by parts

This module turns the closed first derivative of CGL's literal kernel into the
first Fourier integration-by-parts identity.  It is a direct intermediate
layer for the `j = 1` case of CGL Lemma 4.3.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHtFirstDerivative
import Mathlib.Analysis.Fourier.FourierTransformDeriv

open scoped FourierTransform

noncomputable section

namespace RHTower

/-- The derivative of the CGL Schwartz kernel, retained as a Schwartz function. -/
noncomputable def cglSmoothBumpHtDerivative (w : CGLSmoothBump) (t : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ (cglSmoothBumpHt w t)

/-- The derivative Schwartz carrier evaluates to the literal derivative of `h_t`. -/
theorem cglSmoothBumpHtDerivative_apply (w : CGLSmoothBump) (t x : ℝ) :
    cglSmoothBumpHtDerivative w t x = deriv (cglSmoothBumpHtValue w t) x := by
  rw [cglSmoothBumpHtDerivative, SchwartzMap.derivCLM_apply]
  rfl

/-- Fourier transform of the literal CGL kernel derivative. -/
theorem cglSmoothBumpHt_fourier_derivative (w : CGLSmoothBump) (t ξ : ℝ) :
    𝓕 (cglSmoothBumpHtDerivative w t : ℝ → ℂ) ξ =
      (2 * Real.pi * Complex.I * ξ) • 𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ := by
  have h := Real.fourier_deriv (f := (cglSmoothBumpHt w t : ℝ → ℂ))
    (cglSmoothBumpHt w t).integrable (cglSmoothBumpHt w t).differentiable
    (cglSmoothBumpHtDerivative w t).integrable
  exact congrFun h ξ

/-- First integration-by-parts Fourier control for CGL's literal kernel. -/
theorem cglSmoothBumpHt_firstDerivative_fourier_decay (w : CGLSmoothBump) (t ξ : ℝ) :
    (2 * Real.pi) * (|ξ| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) ≤
      cglSchwartzFourierDecayBudget (cglSmoothBumpHtDerivative w t) 0 := by
  have hbudget := cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget
    (cglSmoothBumpHtDerivative w t) 0 ξ
  have hfourier := cglSmoothBumpHt_fourier_derivative w t ξ
  rw [pow_zero, one_mul] at hbudget
  calc
    (2 * Real.pi) * (|ξ| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) =
        ‖𝓕 (cglSmoothBumpHtDerivative w t : ℝ → ℂ) ξ‖ := by
      rw [hfourier, norm_smul]
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs]
      norm_num
      rw [abs_of_pos Real.pi_pos]
      ring
    _ ≤ cglSchwartzFourierDecayBudget (cglSmoothBumpHtDerivative w t) 0 := hbudget

end RHTower
