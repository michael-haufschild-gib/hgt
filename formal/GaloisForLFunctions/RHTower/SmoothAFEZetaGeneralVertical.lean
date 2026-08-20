import GaloisForLFunctions.RHTower.GaussianShiftedMoment
import GaloisForLFunctions.RHTower.ZetaVerticalLineGrowth
import GaloisForLFunctions.RHTower.SmoothAFEZetaMellin

/-!
# Vertical integrability of the smooth-AFE integrand at a general point

The corpus proves the two vertical edges of the smooth-AFE rectangle integrable only on the critical
line, and the right edge only when `Re s + c > 1`.  Both restrictions disappear once the zeta factor
is majorised by the vertical polynomial growth bound: the Gaussian kernel supplies `exp(-v²)` and the
shifted polynomial moment is integrable against it.

The only hypotheses are that the edge misses the origin (`c ≠ 0`, so the kernel's pole is avoided)
and misses the pole abscissa (`Re s + c ≠ 1`).
-/

open Complex MeasureTheory

noncomputable section

namespace RHTower

theorem smoothAFEZetaMellinIntegrand_vertical_point {s : ℂ} {c v : ℝ} :
    s + ((c : ℂ) + (v : ℂ) * I) = ((s.re + c : ℝ) : ℂ) + ((s.im + v : ℝ) : ℂ) * I := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

theorem norm_smoothAFEZetaMellinIntegrand_vertical_general_le
    {x : ℝ} (hx : 0 < x) {s : ℂ} {c : ℝ} (hc : c ≠ 0) {C : ℝ} (hC0 : 0 ≤ C) {N : ℕ}
    (hC : ∀ t : ℝ, ‖riemannZeta (((s.re + c : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N)
    (v : ℝ) :
    ‖smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (v : ℂ) * I)‖
      ≤ (C * (x ^ c * (Real.exp (c ^ 2) / |c|)))
        * (((1 + |s.im|) + |v|) ^ N * Real.exp (-v ^ 2)) := by
  set w : ℂ := (c : ℂ) + (v : ℂ) * I with hw
  have hcabs : (0 : ℝ) < |c| := abs_pos.mpr hc
  have hwre : w.re = c := by rw [hw]; simp
  have hwim : w.im = v := by rw [hw]; simp
  have hwnorm : |c| ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    rw [hwre] at h
    exact h
  have hzeta : ‖riemannZeta (s + w)‖ ≤ C * ((1 + |s.im|) + |v|) ^ N := by
    rw [hw, smoothAFEZetaMellinIntegrand_vertical_point]
    refine le_trans (hC (s.im + v)) ?_
    have hmono : (1 + |s.im + v|) ^ N ≤ ((1 + |s.im|) + |v|) ^ N := by
      refine pow_le_pow_left₀ (by positivity) ?_ N
      have := abs_add_le s.im v
      linarith
    exact mul_le_mul_of_nonneg_left hmono hC0
  have hpow : ‖(x : ℂ) ^ w‖ = x ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hwre]
  have hker : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp (c ^ 2) / |c| * Real.exp (-v ^ 2) := by
    have hre : (w ^ 2).re = c ^ 2 - v ^ 2 := by
      rw [hw, pow_two]
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    have hexp : ‖Complex.exp (w ^ 2)‖ = Real.exp (c ^ 2 - v ^ 2) := by
      rw [Complex.norm_exp, hre]
    rw [smoothAFEGaussianKernel, norm_div, hexp, Real.exp_sub]
    rw [div_le_iff₀ (lt_of_lt_of_le hcabs hwnorm)]
    have hstep : Real.exp (c ^ 2) / Real.exp (v ^ 2) = Real.exp (c ^ 2) * Real.exp (-v ^ 2) := by
      rw [Real.exp_neg]
      ring
    rw [hstep]
    have hfac : Real.exp (c ^ 2) * Real.exp (-v ^ 2)
        ≤ Real.exp (c ^ 2) / |c| * Real.exp (-v ^ 2) * ‖w‖ := by
      have h1 : Real.exp (c ^ 2) / |c| * Real.exp (-v ^ 2) * |c|
          = Real.exp (c ^ 2) * Real.exp (-v ^ 2) := by
        field_simp
      calc Real.exp (c ^ 2) * Real.exp (-v ^ 2)
          = Real.exp (c ^ 2) / |c| * Real.exp (-v ^ 2) * |c| := h1.symm
        _ ≤ Real.exp (c ^ 2) / |c| * Real.exp (-v ^ 2) * ‖w‖ := by
            refine mul_le_mul_of_nonneg_left hwnorm ?_
            positivity
    exact hfac
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul, hpow]
  have hxc : (0 : ℝ) < x ^ c := Real.rpow_pos_of_pos hx c
  have hzn : (0 : ℝ) ≤ C * ((1 + |s.im|) + |v|) ^ N := by
    have : (0 : ℝ) ≤ (1 + |s.im|) + |v| := by positivity
    positivity
  calc ‖riemannZeta (s + w)‖ * x ^ c * ‖smoothAFEGaussianKernel w‖
      ≤ (C * ((1 + |s.im|) + |v|) ^ N) * x ^ c
          * (Real.exp (c ^ 2) / |c| * Real.exp (-v ^ 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hzeta hxc.le) hker (norm_nonneg _) ?_
        positivity
    _ = (C * (x ^ c * (Real.exp (c ^ 2) / |c|)))
          * (((1 + |s.im|) + |v|) ^ N * Real.exp (-v ^ 2)) := by ring

theorem continuous_smoothAFEZetaMellinIntegrand_vertical
    {x : ℝ} (hx : 0 < x) {s : ℂ} {c : ℝ} (hc : c ≠ 0) (hsc : s.re + c ≠ 1) :
    Continuous fun v : ℝ => smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (v : ℂ) * I) := by
  have hpath : Continuous fun v : ℝ => (c : ℂ) + (v : ℂ) * I := by fun_prop
  have hne1 : ∀ v : ℝ, s + ((c : ℂ) + (v : ℂ) * I) ≠ 1 := by
    intro v h
    rw [smoothAFEZetaMellinIntegrand_vertical_point] at h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re] at hre
    exact hsc (by linarith)
  have hne0 : ∀ v : ℝ, ((c : ℂ) + (v : ℂ) * I) ≠ 0 := by
    intro v h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at hre
    exact hc (by linarith)
  have hz : Continuous fun v : ℝ => riemannZeta (s + ((c : ℂ) + (v : ℂ) * I)) := by
    refine continuous_iff_continuousAt.mpr fun v => ?_
    have hc1 : ContinuousAt (fun u : ℝ => s + ((c : ℂ) + (u : ℂ) * I)) v := by fun_prop
    have hc2 : ContinuousAt riemannZeta (s + ((c : ℂ) + (v : ℂ) * I)) :=
      (differentiableAt_riemannZeta (hne1 v)).continuousAt
    have hcomp : ContinuousAt (riemannZeta ∘ fun u : ℝ => s + ((c : ℂ) + (u : ℂ) * I)) v :=
      ContinuousAt.comp hc2 hc1
    simpa [Function.comp_def] using hcomp
  have hp : Continuous fun v : ℝ => ((x : ℂ)) ^ ((c : ℂ) + (v : ℂ) * I) := by
    refine Continuous.cpow continuous_const hpath ?_
    intro v
    left
    exact hx
  have hk : Continuous fun v : ℝ => smoothAFEGaussianKernel ((c : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEGaussianKernel
    exact (Complex.continuous_exp.comp (hpath.pow 2)).div hpath hne0
  exact (hz.mul hp).mul hk

/-- **Vertical integrability of the smooth-AFE integrand at a general base point.** -/
theorem smoothAFEZetaMellinIntegrand_verticalIntegrable_general
    {x : ℝ} (hx : 0 < x) {s : ℂ} {c : ℝ} (hc : c ≠ 0) (hsc : s.re + c ≠ 1) :
    Complex.VerticalIntegrable (smoothAFEZetaMellinIntegrand s x) c := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_vertical (s.re + c) hsc
  rw [Complex.VerticalIntegrable]
  set K : ℝ := C * (x ^ c * (Real.exp (c ^ 2) / |c|)) with hK
  refine Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |s.im|) N).const_mul K)
    (continuous_smoothAFEZetaMellinIntegrand_vertical hx hc hsc).aestronglyMeasurable ?_
  filter_upwards with v
  exact norm_smoothAFEZetaMellinIntegrand_vertical_general_le hx hc hC0 hC v

end RHTower

end
