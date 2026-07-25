import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Gaussian Mellin kernel for the smooth approximate functional equation

This module begins the unconditional smooth approximate functional equation used in the
Bourgain critical-line reduction.  It fixes the standard entire numerator

`G(w) = exp(w²)`

and the inverse-Mellin kernel `G(w) / w`.  On every positive vertical line the pole at zero is
avoided and the identity

`‖exp((σ + it)²)‖ = exp(σ²) exp(-t²)`

gives absolute convergence.  The same proof includes the complete inverse-Mellin integrand
`x⁻ʷ G(w) / w` for every `x > 0`.

No zeta-function estimate or asymptotic hypothesis enters these lemmas.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

/-- Meromorphic kernel `exp(w²) / w` used for the smooth approximate functional equation. -/
def smoothAFEGaussianKernel (w : ℂ) : ℂ :=
  Complex.exp (w ^ 2) / w

/-- Full inverse-Mellin integrand for the Gaussian cutoff. -/
def smoothAFEMellinIntegrand (x : ℝ) (w : ℂ) : ℂ :=
  (x : ℂ) ^ (-w) * smoothAFEGaussianKernel w

/-- Explicit Gaussian majorant for the kernel on a positive vertical line. -/
theorem norm_smoothAFEGaussianKernel_vertical_le
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖smoothAFEGaussianKernel ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (Real.exp (σ ^ 2) / σ) * Real.exp (-(t ^ 2)) := by
  have hre :
      ((((σ : ℂ) + (t : ℂ) * I) ^ 2).re) = σ ^ 2 - t ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hden :
      σ ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
    calc
      σ = |(((σ : ℂ) + (t : ℂ) * I)).re| := by simp [abs_of_pos hσ]
      _ ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := Complex.abs_re_le_norm _
  unfold smoothAFEGaussianKernel
  rw [norm_div, Complex.norm_exp, hre,
    show σ ^ 2 - t ^ 2 = σ ^ 2 + (-(t ^ 2)) by ring, Real.exp_add]
  calc
    Real.exp (σ ^ 2) * Real.exp (-(t ^ 2)) /
          ‖(σ : ℂ) + (t : ℂ) * I‖
        ≤ Real.exp (σ ^ 2) * Real.exp (-(t ^ 2)) / σ := by
          exact div_le_div_of_nonneg_left (by positivity) hσ hden
    _ = (Real.exp (σ ^ 2) / σ) * Real.exp (-(t ^ 2)) := by ring

/-- The Gaussian kernel is absolutely integrable on every line `Re w = σ > 0`. -/
theorem smoothAFEGaussianKernel_verticalIntegrable
    {σ : ℝ} (hσ : 0 < σ) :
    Complex.VerticalIntegrable smoothAFEGaussianKernel σ := by
  rw [Complex.VerticalIntegrable]
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (Real.exp (σ ^ 2) / σ))
  · exact (continuous_exp.comp (by fun_prop)).div
      (by fun_prop)
      (fun t hzero => by
        have hre : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
        rw [← hre] at hσ
        exact (hσ.ne' (congrArg Complex.re hzero)).elim)
      |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      simpa [smoothAFEGaussianKernel] using
        norm_smoothAFEGaussianKernel_vertical_le hσ t

/-- Explicit Gaussian majorant for the full inverse-Mellin integrand. -/
theorem norm_smoothAFEMellinIntegrand_vertical_le
    {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (t : ℝ) :
    ‖smoothAFEMellinIntegrand x ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (x ^ (-σ) * (Real.exp (σ ^ 2) / σ)) * Real.exp (-(t ^ 2)) := by
  rw [smoothAFEMellinIntegrand, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  calc
    x ^ (-σ) * ‖smoothAFEGaussianKernel ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ x ^ (-σ) * ((Real.exp (σ ^ 2) / σ) * Real.exp (-(t ^ 2))) := by
          exact mul_le_mul_of_nonneg_left
            (norm_smoothAFEGaussianKernel_vertical_le hσ t) (by positivity)
    _ = (x ^ (-σ) * (Real.exp (σ ^ 2) / σ)) * Real.exp (-(t ^ 2)) := by ring

/-- The complete Gaussian inverse-Mellin integrand is absolutely integrable on every positive
vertical line. -/
theorem smoothAFEMellinIntegrand_verticalIntegrable
    {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (smoothAFEMellinIntegrand x) σ := by
  rw [Complex.VerticalIntegrable]
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (x ^ (-σ) * (Real.exp (σ ^ 2) / σ)))
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    exact (((continuous_const_cpow (x : ℂ)).comp (by fun_prop)).mul
      ((continuous_exp.comp (by fun_prop)).div
        (by fun_prop)
        (fun t hzero => by
          have hre : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
          rw [← hre] at hσ
          exact (hσ.ne' (congrArg Complex.re hzero)).elim))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      simpa using norm_smoothAFEMellinIntegrand_vertical_le hx hσ t

/-- Gaussian cutoff, initially defined on an arbitrary positive inverse-Mellin abscissa.  A
following contour-shift module proves independence of that abscissa. -/
def smoothAFECutoffAt (σ x : ℝ) : ℂ :=
  mellinInv σ smoothAFEGaussianKernel x

end RHTower
