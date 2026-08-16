import Mathlib

/-!
# Vertical means of the characters `t ↦ e^{iθt}`

The mean of a nontrivial character over a symmetric vertical segment vanishes in the limit:

```text
(1/2T) ∫_{−T}^{T} e^{iθt} dt  =  sin(θT)/(θT)  →  0        (θ ≠ 0) ,
```

while for `θ = 0` the mean is identically one.  The proof of the bound needs no trigonometry: the
antiderivative of `e^{ct}` is `e^{ct}/c`, and both endpoint values are unimodular, so the integral is
at most `2/|θ|` in modulus — uniformly in `T`.

This is the orthogonality relation behind Bohr's coefficient estimates for Dirichlet series: applied
to `θ = log((m+1)/(n+1))` it separates the `m`-th term from the `n`-th.
-/

noncomputable section

open Filter Topology intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- The exponential integral over a real interval. -/
theorem integral_cexp_const_mul {c : ℂ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ t in a..b, Complex.exp (c * (t : ℂ))
      = (Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))) / c := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (c * (u : ℂ)) / c)
      (Complex.exp (c * (t : ℂ))) t := by
    intro t
    have h0 : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => c * ((u : ℝ) : ℂ)) c t := by
      simpa using h0.const_mul c
    have h2 := h1.cexp
    have h3 := h2.div_const c
    have h4 : c * (Complex.exp (c * (t : ℂ)) / c) = Complex.exp (c * (t : ℂ)) := by
      field_simp
    have h5 : Complex.exp (c * (t : ℂ)) * c / c = Complex.exp (c * (t : ℂ)) := by
      field_simp
    rw [h5] at h3
    exact h3
  have hcont : ContinuousOn (fun t : ℝ => Complex.exp (c * (t : ℂ))) (Set.uIcc a b) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    hcont.intervalIntegrable, sub_div]

/-- **The vertical integral of a nontrivial character is bounded uniformly in the length.** -/
theorem norm_integral_cexp_I_le {θ : ℝ} (hθ : θ ≠ 0) (T : ℝ) :
    ‖∫ t in (-T)..T, Complex.exp (((θ : ℂ) * Complex.I) * (t : ℂ))‖ ≤ 2 / |θ| := by
  have hc : ((θ : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.ext_iff, hθ]
  rw [integral_cexp_const_mul hc]
  have hnorm : ∀ u : ℝ, ‖Complex.exp (((θ : ℂ) * Complex.I) * (u : ℂ))‖ = 1 := by
    intro u
    rw [Complex.norm_exp]
    norm_num
  have hcn : ‖((θ : ℂ) * Complex.I)‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_div, hcn]
  have habs : (0 : ℝ) < |θ| := abs_pos.2 hθ
  have hnum : ‖Complex.exp (((θ : ℂ) * Complex.I) * ((T : ℝ) : ℂ))
      - Complex.exp (((θ : ℂ) * Complex.I) * ((-T : ℝ) : ℂ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [hnorm, hnorm]
    norm_num
  gcongr

/-- **The vertical mean of a nontrivial character vanishes.** -/
theorem tendsto_vertical_mean_cexp {θ : ℝ} (hθ : θ ≠ 0) :
    Tendsto (fun T : ℝ =>
      (1 / (2 * T)) * ‖∫ t in (-T)..T, Complex.exp (((θ : ℂ) * Complex.I) * (t : ℂ))‖)
      atTop (𝓝 0) := by
  have hmaj : Tendsto (fun T : ℝ => (1 / (2 * T)) * (2 / |θ|)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 1 / (2 * T)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun T : ℝ => 2 * T) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (show (0 : ℝ) < 2 by norm_num) tendsto_id
      have h3 := h2.inv_tendsto_atTop
      refine h3.congr fun T => ?_
      simp [one_div]
    simpa using h1.mul_const (2 / |θ|)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hpos : (0 : ℝ) < 1 / (2 * T) := by positivity
    exact mul_le_mul_of_nonneg_left (norm_integral_cexp_I_le hθ T) hpos.le

/-- The trivial character has mean one. -/
theorem integral_cexp_zero_mul (T : ℝ) :
    ∫ t in (-T)..T, Complex.exp ((0 : ℂ) * (t : ℂ)) = (2 * T : ℝ) := by
  simp
  ring

end GaloisForLFunctions.RHTower

end
