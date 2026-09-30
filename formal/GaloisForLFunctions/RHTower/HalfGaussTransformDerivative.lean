import GaloisForLFunctions.RHTower.HeatGaussianTiltedMoments

/-!
# Differentiating a one-sided Gaussian average in its centre

For `t > 0` and `F : ℝ → ℂ` continuous with `e^{−w²/(16t)} ‖F(w)‖` integrable, the one-sided average

`Q(y) = ∫_0^∞ g_t(w − y) F(w) dw`

is differentiable with `Q'(y) = ∫_0^∞ ((w − y)/(2t)) g_t(w − y) F(w) dw`
(`hasDerivAt_halfGaussTransform`). Domination: `(w−y)² ≥ w²/2 − y²` and `|u| e^{−u²/(8t)} ≤ 1 + 8t`
give `(|w − y|/(2t)) g_t(w − y) ≤ ((1 + 8t)/t) e^{y²/(8t)} e^{−w²/(16t)}`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- The one-sided Gaussian average `Q(y) = ∫_0^∞ g_t(w − y) F(w) dw`. -/
def halfGaussTransform (t : ℝ) (F : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ w in Ioi (0 : ℝ), (gaussDensity t (w - y) : ℂ) * F w

theorem halfGaussAverage_eq_halfGaussTransform (t X y : ℝ) :
    halfGaussAverage t X y = halfGaussTransform t (fun w => xi (1 / 2 + w + I * X)) y := rfl

theorem continuous_gaussDensity (t : ℝ) : Continuous (gaussDensity t) := by
  unfold gaussDensity; fun_prop

theorem hasDerivAt_gaussDensity_sub {t : ℝ} (w y : ℝ) :
    HasDerivAt (fun y => gaussDensity t (w - y)) (gaussDensity t (w - y) * ((w - y) / (2 * t))) y := by
  have h1 : HasDerivAt (fun y : ℝ => -((w - y) ^ 2 / (4 * t))) ((w - y) / (2 * t)) y := by
    have h := ((((hasDerivAt_id' y).const_sub w).pow 2).div_const (4 * t)).neg
    refine h.congr_deriv ?_
    norm_num
    ring
  have h2 := h1.exp.const_mul ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)))
  unfold gaussDensity
  refine h2.congr_deriv ?_
  ring

/-- `(w − y)² ≥ w²/2 − y²`. -/
theorem half_sq_sub_sq_le (w y : ℝ) : w ^ 2 / 2 - y ^ 2 ≤ (w - y) ^ 2 := by
  nlinarith [sq_nonneg (w - 2 * y)]

theorem abs_mul_exp_neg_sq_le {t : ℝ} (ht : 0 < t) (u : ℝ) :
    |u| * Real.exp (-(u ^ 2 / (8 * t))) ≤ 1 + 8 * t := by
  have h1 : |u| ≤ 1 + u ^ 2 := by nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
  have h2 : u ^ 2 * Real.exp (-(u ^ 2 / (8 * t))) ≤ 8 * t := by
    set v := u ^ 2 / (8 * t) with hv
    have hve : v * Real.exp (-v) ≤ 1 := by
      have := Real.add_one_le_exp v
      calc v * Real.exp (-v) ≤ Real.exp v * Real.exp (-v) := by
            gcongr; linarith
        _ = 1 := by rw [← Real.exp_add]; simp
    have hq : u ^ 2 = 8 * t * v := by rw [hv]; field_simp
    rw [hq]
    have h8 : 0 < 8 * t := by positivity
    nlinarith
  have h3 : Real.exp (-(u ^ 2 / (8 * t))) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ u ^ 2 / (8 * t) := by positivity
    linarith)
  have h0 := Real.exp_pos (-(u ^ 2 / (8 * t)))
  nlinarith

/-- The Gaussian at `w − y` is dominated by `e^{y²/(4t)}` times the Gaussian of variance `8t` at
`w`, up to the normalization `(4πt)^{−1/2}`. -/
theorem gaussDensity_sub_le {t : ℝ} (ht : 0 < t) (w y : ℝ) :
    gaussDensity t (w - y) ≤
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (y ^ 2 / (4 * t)) *
        Real.exp (-(w ^ 2 / (16 * t))) := by
  unfold gaussDensity
  have hexp : Real.exp (-((w - y) ^ 2 / (4 * t))) ≤
      Real.exp (y ^ 2 / (4 * t)) * Real.exp (-(w ^ 2 / (16 * t))) := by
    rw [← Real.exp_add]
    gcongr
    have := half_sq_sub_sq_le w y
    have h4 : 0 < 4 * t := by positivity
    have h1 : (w ^ 2 / 2 - y ^ 2) / (4 * t) ≤ (w - y) ^ 2 / (4 * t) := by gcongr
    have e : (w ^ 2 / 2 - y ^ 2) / (4 * t) = w ^ 2 / (8 * t) - y ^ 2 / (4 * t) := by
      field_simp; ring
    have e2 : w ^ 2 / (16 * t) ≤ w ^ 2 / (8 * t) := by
      gcongr; linarith
    linarith
  calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - y) ^ 2 / (4 * t)))
      ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (y ^ 2 / (4 * t)) * Real.exp (-(w ^ 2 / (16 * t)))) := by gcongr
    _ = _ := by ring

theorem abs_mul_gaussDensity_sub_le {t : ℝ} (ht : 0 < t) (w y : ℝ) :
    |(w - y) / (2 * t)| * gaussDensity t (w - y) ≤
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * ((1 + 8 * t) / (2 * t)) * Real.exp (y ^ 2 / (8 * t)) *
        Real.exp (-(w ^ 2 / (16 * t))) := by
  unfold gaussDensity
  have hsplit : Real.exp (-((w - y) ^ 2 / (4 * t))) =
      Real.exp (-((w - y) ^ 2 / (8 * t))) * Real.exp (-((w - y) ^ 2 / (8 * t))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hA := abs_mul_exp_neg_sq_le ht (w - y)
  have hB : Real.exp (-((w - y) ^ 2 / (8 * t))) ≤
      Real.exp (y ^ 2 / (8 * t)) * Real.exp (-(w ^ 2 / (16 * t))) := by
    rw [← Real.exp_add]
    gcongr
    have := half_sq_sub_sq_le w y
    have h8 : 0 < 8 * t := by positivity
    have : (w ^ 2 / 2 - y ^ 2) / (8 * t) ≤ (w - y) ^ 2 / (8 * t) := by gcongr
    have e : (w ^ 2 / 2 - y ^ 2) / (8 * t) = w ^ 2 / (16 * t) - y ^ 2 / (8 * t) := by
      field_simp; ring
    linarith
  rw [hsplit, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
  have hc : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
  calc |w - y| / (2 * t) * ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (-((w - y) ^ 2 / (8 * t))) * Real.exp (-((w - y) ^ 2 / (8 * t)))))
      = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) / (2 * t) *
          (|w - y| * Real.exp (-((w - y) ^ 2 / (8 * t)))) *
          Real.exp (-((w - y) ^ 2 / (8 * t))) := by ring
    _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) / (2 * t) * (1 + 8 * t) *
          (Real.exp (y ^ 2 / (8 * t)) * Real.exp (-(w ^ 2 / (16 * t)))) := by
        gcongr
    _ = _ := by ring

theorem integrable_gaussDensity_sub_mul {t : ℝ} (ht : 0 < t) {F : ℝ → ℂ} (hF : Continuous F)
    (hint : Integrable (fun w => Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖)) (y : ℝ) :
    Integrable (fun w => (gaussDensity t (w - y) : ℂ) * F w) := by
  refine (hint.const_mul ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (y ^ 2 / (4 * t)))).mono'
    ((Complex.continuous_ofReal.comp ((continuous_gaussDensity t).comp
      (continuous_id.sub continuous_const))).mul hF).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht _)]
  have := gaussDensity_sub_le ht w y
  calc gaussDensity t (w - y) * ‖F w‖
      ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (y ^ 2 / (4 * t)) *
          Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖ := by gcongr
    _ = _ := by ring

theorem integrable_slope_mul {t : ℝ} (ht : 0 < t) {F : ℝ → ℂ} (hF : Continuous F)
    (hint : Integrable (fun w => Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖)) (y : ℝ) :
    Integrable (fun w => (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) := by
  refine (hint.const_mul ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * ((1 + 8 * t) / (2 * t)) *
    Real.exp (y ^ 2 / (8 * t)))).mono' ?_ (Eventually.of_forall fun w => ?_)
  · refine (Continuous.mul ?_ hF).aestronglyMeasurable
    exact Complex.continuous_ofReal.comp (by
      have := continuous_gaussDensity t
      fun_prop)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (gaussDensity_pos ht _)]
    have := abs_mul_gaussDensity_sub_le ht w y
    calc |(w - y) / (2 * t)| * gaussDensity t (w - y) * ‖F w‖
        ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * ((1 + 8 * t) / (2 * t)) *
            Real.exp (y ^ 2 / (8 * t)) * Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖ := by gcongr
      _ = _ := by ring

/-- **Differentiation under the integral.** -/
theorem hasDerivAt_halfGaussTransform {t : ℝ} (ht : 0 < t) {F : ℝ → ℂ} (hF : Continuous F)
    (hint : Integrable (fun w => Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖)) (y₀ : ℝ) :
    HasDerivAt (halfGaussTransform t F)
      (∫ w in Ioi (0 : ℝ), (((w - y₀) / (2 * t) * gaussDensity t (w - y₀) : ℝ) : ℂ) * F w) y₀ := by
  set c : ℝ := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := by positivity
  set Kd : ℝ := c * ((1 + 8 * t) / (2 * t)) * Real.exp ((|y₀| + 1) ^ 2 / (8 * t)) with hKd
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable
      (fun w => (gaussDensity t (w - y) : ℂ) * F w) (volume.restrict (Ioi 0)) := by
    intro y
    exact ((Complex.continuous_ofReal.comp ((continuous_gaussDensity t).comp
      (continuous_id.sub continuous_const))).mul hF).aestronglyMeasurable
  have hint0 : Integrable (fun w => (gaussDensity t (w - y₀) : ℂ) * F w)
      (volume.restrict (Ioi 0)) := by
    refine ((hint.const_mul (c * Real.exp (y₀ ^ 2 / (4 * t)))).integrableOn).mono'
      (hmeas y₀) (Eventually.of_forall fun w => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht _)]
    have := gaussDensity_sub_le ht w y₀
    calc gaussDensity t (w - y₀) * ‖F w‖
        ≤ c * Real.exp (y₀ ^ 2 / (4 * t)) * Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖ := by
          gcongr
      _ = _ := by ring
  have hmeas' : AEStronglyMeasurable
      (fun w => (((w - y₀) / (2 * t) * gaussDensity t (w - y₀) : ℝ) : ℂ) * F w)
      (volume.restrict (Ioi 0)) := by
    refine (Continuous.mul ?_ hF).aestronglyMeasurable
    exact Complex.continuous_ofReal.comp (by
      have := continuous_gaussDensity t
      fun_prop)
  have hbound : ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))), ∀ y ∈ Metric.ball y₀ 1,
      ‖(((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w‖ ≤
        Kd * (Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖) := by
    refine Eventually.of_forall fun w y hy => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (gaussDensity_pos ht _)]
    have h1 := abs_mul_gaussDensity_sub_le ht w y
    have hy : |y| ≤ |y₀| + 1 := by
      have := Metric.mem_ball.mp hy
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub y y₀
      linarith
    have hy2 : y ^ 2 ≤ (|y₀| + 1) ^ 2 := by
      rw [← sq_abs y]; gcongr
    have hexp : Real.exp (y ^ 2 / (8 * t)) ≤ Real.exp ((|y₀| + 1) ^ 2 / (8 * t)) := by
      gcongr
    calc |(w - y) / (2 * t)| * gaussDensity t (w - y) * ‖F w‖
        ≤ c * ((1 + 8 * t) / (2 * t)) * Real.exp (y ^ 2 / (8 * t)) *
            Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖ := by gcongr
      _ ≤ c * ((1 + 8 * t) / (2 * t)) * Real.exp ((|y₀| + 1) ^ 2 / (8 * t)) *
            Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖ := by gcongr
      _ = _ := by rw [hKd]; ring
  have hderiv : ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))), ∀ y ∈ Metric.ball y₀ 1,
      HasDerivAt (fun y => (gaussDensity t (w - y) : ℂ) * F w)
        ((((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) y := by
    refine Eventually.of_forall fun w y _ => ?_
    have := ((hasDerivAt_gaussDensity_sub (t := t) w y).ofReal_comp).mul_const (F w)
    exact this.congr_deriv (by push_cast; ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds y₀ one_pos)
    (Eventually.of_forall hmeas) hint0 hmeas' hbound
    ((hint.const_mul Kd).integrableOn) hderiv).2

end

end RHTower.DeBruijn
