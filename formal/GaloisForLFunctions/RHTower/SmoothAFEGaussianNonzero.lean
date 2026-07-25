import GaloisForLFunctions.RHTower.SmoothAFEGaussianKernel

/-!
# Gaussian Mellin bounds on nonzero vertical lines

For the residue shift in the smooth approximate functional equation, the Gaussian Mellin
integrand must also be controlled to the left of its pole at zero.  These lemmas extend the
positive-line estimates to every `σ ≠ 0`, with denominator `|σ|`.  In particular, both vertical
sides of any residue-crossing rectangle are absolutely integrable.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

theorem norm_smoothAFEGaussianKernel_vertical_le_of_ne
    {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    ‖smoothAFEGaussianKernel ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (Real.exp (σ ^ 2) / |σ|) * Real.exp (-(t ^ 2)) := by
  have hre :
      ((((σ : ℂ) + (t : ℂ) * I) ^ 2).re) = σ ^ 2 - t ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hden :
      |σ| ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
    calc
      |σ| = |(((σ : ℂ) + (t : ℂ) * I)).re| := by simp
      _ ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := Complex.abs_re_le_norm _
  have habs : 0 < |σ| := abs_pos.mpr hσ
  unfold smoothAFEGaussianKernel
  rw [norm_div, Complex.norm_exp, hre,
    show σ ^ 2 - t ^ 2 = σ ^ 2 + (-(t ^ 2)) by ring, Real.exp_add]
  calc
    Real.exp (σ ^ 2) * Real.exp (-(t ^ 2)) /
          ‖(σ : ℂ) + (t : ℂ) * I‖
        ≤ Real.exp (σ ^ 2) * Real.exp (-(t ^ 2)) / |σ| := by
          exact div_le_div_of_nonneg_left (by positivity) habs hden
    _ = (Real.exp (σ ^ 2) / |σ|) * Real.exp (-(t ^ 2)) := by ring

theorem smoothAFEGaussianKernel_verticalIntegrable_of_ne
    {σ : ℝ} (hσ : σ ≠ 0) :
    Complex.VerticalIntegrable smoothAFEGaussianKernel σ := by
  rw [Complex.VerticalIntegrable]
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (Real.exp (σ ^ 2) / |σ|))
  · exact (continuous_exp.comp (by fun_prop)).div
      (by fun_prop)
      (fun t hzero => by
        have hre : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
        rw [← hre] at hσ
        exact (hσ (congrArg Complex.re hzero)).elim)
      |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      simpa [smoothAFEGaussianKernel] using
        norm_smoothAFEGaussianKernel_vertical_le_of_ne hσ t

theorem norm_smoothAFEMellinIntegrand_vertical_le_of_ne
    {x σ : ℝ} (hx : 0 < x) (hσ : σ ≠ 0) (t : ℝ) :
    ‖smoothAFEMellinIntegrand x ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (x ^ (-σ) * (Real.exp (σ ^ 2) / |σ|)) * Real.exp (-(t ^ 2)) := by
  rw [smoothAFEMellinIntegrand, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  calc
    x ^ (-σ) * ‖smoothAFEGaussianKernel ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ x ^ (-σ) * ((Real.exp (σ ^ 2) / |σ|) * Real.exp (-(t ^ 2))) := by
          exact mul_le_mul_of_nonneg_left
            (norm_smoothAFEGaussianKernel_vertical_le_of_ne hσ t) (by positivity)
    _ = (x ^ (-σ) * (Real.exp (σ ^ 2) / |σ|)) * Real.exp (-(t ^ 2)) := by ring

theorem smoothAFEMellinIntegrand_verticalIntegrable_of_ne
    {x σ : ℝ} (hx : 0 < x) (hσ : σ ≠ 0) :
    Complex.VerticalIntegrable (smoothAFEMellinIntegrand x) σ := by
  rw [Complex.VerticalIntegrable]
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (x ^ (-σ) * (Real.exp (σ ^ 2) / |σ|)))
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    exact (((continuous_const_cpow (x : ℂ)).comp (by fun_prop)).mul
      ((continuous_exp.comp (by fun_prop)).div
        (by fun_prop)
        (fun t hzero => by
          have hre : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
          rw [← hre] at hσ
          exact (hσ (congrArg Complex.re hzero)).elim))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      simpa using norm_smoothAFEMellinIntegrand_vertical_le_of_ne hx hσ t

end RHTower
