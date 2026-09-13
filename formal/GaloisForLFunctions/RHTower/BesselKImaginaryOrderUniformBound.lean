import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct

/-!
# A uniform bound for the modified Bessel function of imaginary order

For `x > 0` the whole-line Schläfli integral `∫_ℝ exp(−x cosh u + ν u) du = 2 K_x(ν)` may be shifted to
the horizontal line `Im u = θ` for any `0 ≤ θ < π/2`: the integrand is entire and its modulus on the
vertical sides of the rectangle `[−R, R] × [0, θ]` is at most `exp(−x cos θ cosh R + ‖ν‖(R + θ))`,
which tends to zero.  On the shifted line the modulus of the integrand at order `ν = iτ` is
`exp(−x cos θ cosh u)·exp(−τθ)`, so

`‖K_x(iτ)‖ ≤ exp(−τθ) · ∫₀^∞ exp(−x cos θ cosh u) du`.

The remaining integral is at most `log(2/y) + 1` for `y = x cos θ ≤ 2`, by `cosh u ≥ e^u/2` and the
elementary tail estimate.  Choosing `θ = π/2 − 1/τ` and using `sin(1/τ) ≥ 2/(πτ)` gives, for
`x ≥ 1` and `τ ≥ 1`,

`‖K_x(iτ)‖ ≤ e · (log(πτ) + 1) · exp(−πτ/2)`.

This is the exponential-precision decay in the order that the cusp part of the completed Eisenstein
series `E*(·, 1/2 + it)` inherits from its Whittaker coefficients.
-/

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The entire Schläfli integrand as a function of a complex variable. -/
def besselOrderEntireKernel (x : ℝ) (ν : ℂ) (w : ℂ) : ℂ :=
  Complex.exp (-(x : ℂ) * Complex.cosh w + ν * w)

theorem differentiable_besselOrderEntireKernel (x : ℝ) (ν : ℂ) :
    Differentiable ℂ (besselOrderEntireKernel x ν) := by
  unfold besselOrderEntireKernel
  fun_prop

theorem besselOrderEntireKernel_ofReal (x : ℝ) (ν : ℂ) (t : ℝ) :
    besselOrderEntireKernel x ν (t : ℂ) = besselOrderExpKernel x ν t := rfl

/-- Real part of `cosh` at a complex point. -/
theorem cosh_re_eq (a b : ℝ) :
    (Complex.cosh ((a : ℂ) + (b : ℂ) * I)).re = Real.cosh a * Real.cos b := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im]

/-- Modulus of the entire kernel at `a + bi`. -/
theorem norm_besselOrderEntireKernel (x : ℝ) (ν : ℂ) (a b : ℝ) :
    ‖besselOrderEntireKernel x ν ((a : ℂ) + (b : ℂ) * I)‖ =
      Real.exp (-x * (Real.cosh a * Real.cos b) + (ν.re * a - ν.im * b)) := by
  unfold besselOrderEntireKernel
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im, cosh_re_eq]
  ring

/-- Bound on the vertical sides: for `|b| ≤ θ < π/2`,
`‖f(a + bi)‖ ≤ exp(−x cos θ cosh a + ‖ν‖(|a| + θ))`. -/
theorem norm_besselOrderEntireKernel_le {x : ℝ} (hx : 0 < x) (ν : ℂ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ < Real.pi / 2) (a : ℝ) {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ θ) :
    ‖besselOrderEntireKernel x ν ((a : ℂ) + (b : ℂ) * I)‖ ≤
      Real.exp (-(x * Real.cos θ) * Real.cosh a + ‖ν‖ * (|a| + θ)) := by
  rw [norm_besselOrderEntireKernel]
  apply Real.exp_le_exp.mpr
  have hcos : Real.cos θ ≤ Real.cos b :=
    Real.cos_le_cos_of_nonneg_of_le_pi hb0 (by linarith [Real.pi_pos]) hb
  have hcosh := Real.cosh_pos a
  have h1 : -x * (Real.cosh a * Real.cos b) ≤ -(x * Real.cos θ) * Real.cosh a := by
    have := mul_le_mul_of_nonneg_left hcos (mul_nonneg hx.le hcosh.le)
    nlinarith
  have hre : ν.re * a ≤ ‖ν‖ * |a| := by
    calc ν.re * a ≤ |ν.re * a| := le_abs_self _
      _ = |ν.re| * |a| := abs_mul _ _
      _ ≤ ‖ν‖ * |a| := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm ν) (abs_nonneg a)
  have him : -(ν.im * b) ≤ ‖ν‖ * θ := by
    calc -(ν.im * b) ≤ |ν.im * b| := neg_le_abs _
      _ = |ν.im| * |b| := abs_mul _ _
      _ ≤ ‖ν‖ * θ := by
          rw [abs_of_nonneg hb0]
          exact mul_le_mul (Complex.abs_im_le_norm ν) hb hb0 (norm_nonneg _)
  nlinarith

/-- The shifted kernel is integrable on the real line. -/
theorem integrable_shifted_besselOrderEntireKernel {x : ℝ} (hx : 0 < x) (ν : ℂ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) :
    Integrable (fun t : ℝ => besselOrderEntireKernel x ν ((t : ℂ) + (θ : ℂ) * I)) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hx' : 0 < x * Real.cos θ := mul_pos hx hcos
  have hbound : Integrable (fun t : ℝ =>
      Real.exp (‖ν‖ * θ) * ‖besselOrderExpKernel (x * Real.cos θ) ((ν.re : ℝ) : ℂ) t‖) :=
    ((integrable_besselOrderExpKernel hx' _).norm).const_mul _
  refine hbound.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · apply Continuous.aestronglyMeasurable
    have : Continuous (fun t : ℝ => ((t : ℂ) + (θ : ℂ) * I)) := by fun_prop
    exact (differentiable_besselOrderEntireKernel x ν).continuous.comp this
  · rw [norm_besselOrderEntireKernel, besselOrderExpKernel, Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hre : (-((x * Real.cos θ : ℝ) : ℂ) * Complex.cosh (t : ℂ) + ((ν.re : ℝ) : ℂ) * (t : ℂ)).re =
        -(x * Real.cos θ) * Real.cosh t + ν.re * t := by
      simp [Complex.add_re, Complex.mul_re, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
        Complex.cos_ofReal_re]
    rw [hre]
    have him : -(ν.im * θ) ≤ ‖ν‖ * θ := by
      calc -(ν.im * θ) ≤ |ν.im * θ| := neg_le_abs _
        _ = |ν.im| * θ := by rw [abs_mul, abs_of_nonneg hθ0]
        _ ≤ ‖ν‖ * θ := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm ν) hθ0
    nlinarith

/-- **Contour shift.**  For `0 ≤ θ < π/2` the Schläfli integral may be taken on `Im u = θ`. -/
theorem integral_besselOrderExpKernel_eq_shifted {x : ℝ} (hx : 0 < x) (ν : ℂ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) :
    (∫ t : ℝ, besselOrderExpKernel x ν t) =
      ∫ t : ℝ, besselOrderEntireKernel x ν ((t : ℂ) + (θ : ℂ) * I) := by
  set f := besselOrderEntireKernel x ν with hf
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  set s : ℝ := x * Real.cos θ with hs
  have hs0 : 0 < s := mul_pos hx hcos
  -- the rectangle identity at width R
  have hrect : ∀ R : ℝ,
      ((∫ u in (-R)..R, f (u : ℂ)) -
        ∫ u in (-R)..R, f ((u : ℂ) + (θ : ℂ) * I)) =
      I • (∫ y in (0 : ℝ)..θ, f (((-R : ℝ) : ℂ) + (y : ℂ) * I)) -
        I • (∫ y in (0 : ℝ)..θ, f ((R : ℂ) + (y : ℂ) * I)) := by
    intro R
    have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((-R : ℝ) : ℂ) ((R : ℂ) + (θ : ℂ) * I)
      ((differentiable_besselOrderEntireKernel x ν).differentiableOn)
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add, Complex.ofReal_zero, zero_mul] at key
    linear_combination key
  -- vertical sides tend to zero
  have hside : ∀ R : ℝ, 0 ≤ R → ∀ a : ℝ, |a| = R →
      ‖∫ y in (0 : ℝ)..θ, f ((a : ℂ) + (y : ℂ) * I)‖ ≤
        θ * Real.exp (-s * Real.cosh R + ‖ν‖ * (R + θ)) := by
    intro R hR a ha
    have hcoshR : Real.cosh a = Real.cosh R := by
      rw [← Real.cosh_abs, ha]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := θ) (f := fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I))
      (C := Real.exp (-s * Real.cosh R + ‖ν‖ * (R + θ))) (fun y hy => by
        rw [Set.uIoc_of_le hθ0] at hy
        have h := norm_besselOrderEntireKernel_le hx ν hθ0 hθ a hy.1.le hy.2
        rw [hcoshR, ha] at h
        exact h)
    rw [sub_zero, abs_of_nonneg hθ0] at this
    linarith
  have hM : Tendsto (fun R : ℝ => 2 * (θ * Real.exp (-s * Real.cosh R + ‖ν‖ * (R + θ))))
      atTop (𝓝 0) := by
    have hle : ∀ R : ℝ, 0 ≤ R →
        Real.exp (-s * Real.cosh R + ‖ν‖ * (R + θ)) ≤
          Real.exp (2 * ‖ν‖ ^ 2 / s + ‖ν‖ * θ) * Real.exp (-(s / 8) * R ^ 2) := by
      intro R hR
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := bessel_exponent_bound s ‖ν‖ hs0 hR
      nlinarith
    have hq : Tendsto (fun R : ℝ => Real.exp (-(s / 8) * R ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => (s / 8) * R ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) (tendsto_pow_atTop two_ne_zero)
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      refine h2.congr (fun R => ?_)
      simp only [Function.comp]
      ring_nf
    have h3 : Tendsto (fun R : ℝ => 2 * (θ * (Real.exp (2 * ‖ν‖ ^ 2 / s + ‖ν‖ * θ) *
        Real.exp (-(s / 8) * R ^ 2)))) atTop (𝓝 0) := by
      have := (hq.const_mul (Real.exp (2 * ‖ν‖ ^ 2 / s + ‖ν‖ * θ))).const_mul θ
      have := this.const_mul 2
      simpa using this
    refine squeeze_zero' (Filter.Eventually.of_forall fun R => by positivity) ?_ h3
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have := hle R hR
    have hθ' : 0 ≤ θ := hθ0
    nlinarith
  -- the difference of truncated integrals tends to zero
  have hdiff0 : Tendsto (fun R : ℝ =>
      (∫ u in (-R)..R, f (u : ℂ)) -
        ∫ u in (-R)..R, f ((u : ℂ) + (θ : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hM
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rw [hrect R]
    have h1 := hside R hR (-R) (by rw [abs_neg, abs_of_nonneg hR])
    have h2 := hside R hR R (abs_of_nonneg hR)
    calc ‖I • (∫ y in (0 : ℝ)..θ, f (((-R : ℝ) : ℂ) + (y : ℂ) * I)) -
          I • (∫ y in (0 : ℝ)..θ, f ((R : ℂ) + (y : ℂ) * I))‖
        ≤ ‖I • (∫ y in (0 : ℝ)..θ, f (((-R : ℝ) : ℂ) + (y : ℂ) * I))‖ +
          ‖I • (∫ y in (0 : ℝ)..θ, f ((R : ℂ) + (y : ℂ) * I))‖ := norm_sub_le _ _
      _ = ‖∫ y in (0 : ℝ)..θ, f (((-R : ℝ) : ℂ) + (y : ℂ) * I)‖ +
          ‖∫ y in (0 : ℝ)..θ, f ((R : ℂ) + (y : ℂ) * I)‖ := by
          simp
      _ ≤ 2 * (θ * Real.exp (-s * Real.cosh R + ‖ν‖ * (R + θ))) := by linarith
  -- the truncated integrals converge to the whole-line integrals
  have hK : Tendsto (fun R : ℝ => ∫ u in (-R)..R, f (u : ℂ)) atTop
      (𝓝 (∫ t : ℝ, f (t : ℂ))) :=
    intervalIntegral_tendsto_integral (f := fun t : ℝ => f (t : ℂ))
      (integrable_besselOrderExpKernel hx ν) tendsto_neg_atTop_atBot tendsto_id
  have hS : Tendsto (fun R : ℝ => ∫ u in (-R)..R, f ((u : ℂ) + (θ : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, f ((t : ℂ) + (θ : ℂ) * I))) :=
    intervalIntegral_tendsto_integral
      (integrable_shifted_besselOrderEntireKernel hx ν hθ0 hθ) tendsto_neg_atTop_atBot tendsto_id
  have hlim := hK.sub hS
  have := tendsto_nhds_unique hlim hdiff0
  exact sub_eq_zero.mp this

/-- The modulus of the shifted kernel at order `iτ`. -/
theorem norm_shifted_kernel_I_mul (x : ℝ) (τ θ t : ℝ) :
    ‖besselOrderEntireKernel x ((τ : ℂ) * I) ((t : ℂ) + (θ : ℂ) * I)‖ =
      Real.exp (-τ * θ) * Real.exp (-(x * Real.cos θ) * Real.cosh t) := by
  rw [norm_besselOrderEntireKernel, ← Real.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- Whole-line integral of an even positive kernel is twice the half-line integral. -/
theorem integral_exp_neg_mul_cosh_eq_two_mul {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, Real.exp (-y * Real.cosh t)) = 2 * ∫ t in Ioi (0 : ℝ), Real.exp (-y * Real.cosh t) := by
  have hint : Integrable (fun t : ℝ => Real.exp (-y * Real.cosh t)) := by
    have h := (integrable_besselOrderExpKernel hy (0 : ℂ)).norm
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [besselOrderExpKernel, Complex.norm_exp, Complex.cosh_ofReal_re]
  have hsplit : (∫ t : ℝ, Real.exp (-y * Real.cosh t)) =
      (∫ t in Iic (0 : ℝ), Real.exp (-y * Real.cosh t)) +
        ∫ t in Ioi (0 : ℝ), Real.exp (-y * Real.cosh t) := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, Set.Iic_union_Ioi]
    exact setIntegral_univ.symm
  have hneg : (∫ t in Iic (0 : ℝ), Real.exp (-y * Real.cosh t)) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-y * Real.cosh t) := by
    have := integral_comp_neg_Iic (0 : ℝ) (fun t : ℝ => Real.exp (-y * Real.cosh t))
    simp only [neg_zero, Real.cosh_neg] at this
    exact this
  rw [hsplit, hneg]
  ring

/-- **Uniform bound via the shifted contour.**  For `0 ≤ θ < π/2` and `τ ≥ 0`,
`‖K_x(iτ)‖ ≤ exp(−τθ)·∫₀^∞ exp(−x cos θ cosh u) du`. -/
theorem norm_modifiedBesselKOrder_I_mul_le_shifted {x : ℝ} (hx : 0 < x) (τ : ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      Real.exp (-τ * θ) * ∫ t in Ioi (0 : ℝ), Real.exp (-(x * Real.cos θ) * Real.cosh t) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hx' : 0 < x * Real.cos θ := mul_pos hx hcos
  have h2 := integral_besselOrderExpKernel_eq_two_mul hx ((τ : ℂ) * I)
  rw [integral_besselOrderExpKernel_eq_shifted hx _ hθ0 hθ] at h2
  have hnorm : ‖∫ t : ℝ, besselOrderEntireKernel x ((τ : ℂ) * I) ((t : ℂ) + (θ : ℂ) * I)‖ ≤
      ∫ t : ℝ, Real.exp (-τ * θ) * Real.exp (-(x * Real.cos θ) * Real.cosh t) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    exact norm_shifted_kernel_I_mul x τ θ t
  rw [integral_const_mul, integral_exp_neg_mul_cosh_eq_two_mul hx'] at hnorm
  have hK : ‖2 * modifiedBesselKOrder x ((τ : ℂ) * I)‖ = 2 * ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ := by
    rw [norm_mul]; norm_num
  rw [h2, hK] at hnorm
  linarith

/-- The elementary tail estimate: for `0 < y ≤ 2`, `∫₀^∞ exp(−y cosh u) du ≤ log(2/y) + 1`. -/
theorem integral_exp_neg_mul_cosh_le {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 2) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-y * Real.cosh t)) ≤ Real.log (2 / y) + 1 := by
  set t₀ : ℝ := Real.log (2 / y) with ht₀
  have ht₀0 : 0 ≤ t₀ := Real.log_nonneg (by rw [le_div_iff₀ hy0]; linarith)
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-y * Real.cosh t)) (Ioi 0) := by
    have h := (integrable_besselOrderExpKernel hy0 (0 : ℂ)).norm.integrableOn (s := Ioi 0)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [besselOrderExpKernel, Complex.norm_exp, Complex.cosh_ofReal_re]
  -- pointwise: exp(−y cosh t) ≤ exp(−(y/2) e^t)
  have hpt : ∀ t : ℝ, Real.exp (-y * Real.cosh t) ≤ Real.exp (-(y / 2) * Real.exp t) := by
    intro t
    apply Real.exp_le_exp.mpr
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-t)]
  -- split at t₀
  have hsplit : (∫ t in Ioi (0 : ℝ), Real.exp (-y * Real.cosh t)) =
      (∫ t in Ioc (0 : ℝ) t₀, Real.exp (-y * Real.cosh t)) +
        ∫ t in Ioi t₀, Real.exp (-y * Real.cosh t) := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi ht₀0)),
      Set.Ioc_union_Ioi_eq_Ioi ht₀0]
  -- first piece: integrand ≤ 1 on a set of measure t₀
  have hfirst : (∫ t in Ioc (0 : ℝ) t₀, Real.exp (-y * Real.cosh t)) ≤ t₀ := by
    calc (∫ t in Ioc (0 : ℝ) t₀, Real.exp (-y * Real.cosh t))
        ≤ ∫ t in Ioc (0 : ℝ) t₀, (1 : ℝ) := by
          refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self)
            ((continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := t₀)).mono_set
              Set.Ioc_subset_Icc_self)
            measurableSet_Ioc (fun t _ => ?_)
          rw [Real.exp_le_one_iff]
          nlinarith [Real.cosh_pos t]
      _ = t₀ := by
          rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real_def, Real.volume_Ioc, sub_zero,
            ENNReal.toReal_ofReal ht₀0]
  -- second piece: for t ≥ t₀, (y/2)e^t = e^{t−t₀} ≥ 1 + (t − t₀)
  have hsecond : (∫ t in Ioi t₀, Real.exp (-y * Real.cosh t)) ≤ 1 := by
    have hexp2 : Real.exp t₀ = 2 / y := by
      rw [ht₀, Real.exp_log (by positivity)]
    have hpt2 : ∀ t ∈ Ioi t₀, Real.exp (-y * Real.cosh t) ≤
        Real.exp (-1 + t₀) * Real.exp (-t) := by
      intro t _
      refine (hpt t).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : Real.exp t = (2 / y) * Real.exp (t - t₀) := by
        rw [← hexp2, ← Real.exp_add]; congr 1; ring
      have h2 : (t - t₀) + 1 ≤ Real.exp (t - t₀) := Real.add_one_le_exp _
      rw [h1]
      have hprod : -(y / 2) * ((2 / y) * Real.exp (t - t₀)) = -Real.exp (t - t₀) := by
        field_simp
      rw [hprod]
      linarith
    calc (∫ t in Ioi t₀, Real.exp (-y * Real.cosh t))
        ≤ ∫ t in Ioi t₀, Real.exp (-1 + t₀) * Real.exp (-t) :=
          setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi ht₀0))
            ((integrableOn_exp_neg_Ioi t₀).const_mul _) measurableSet_Ioi hpt2
      _ = Real.exp (-1 + t₀) * Real.exp (-t₀) := by
          rw [integral_const_mul, integral_exp_neg_Ioi]
      _ ≤ 1 := by
          rw [← Real.exp_add]
          apply Real.exp_le_one_iff.mpr
          linarith
  rw [hsplit]
  linarith

/-- Integrability of the real Schläfli kernel at order zero on the half line. -/
theorem integrableOn_exp_neg_mul_cosh_Ioi {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => Real.exp (-y * Real.cosh t)) (Ioi 0) := by
  have h := (integrable_besselOrderExpKernel hy (0 : ℂ)).norm.integrableOn (s := Ioi 0)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [besselOrderExpKernel, Complex.norm_exp, Complex.cosh_ofReal_re]

/-- **Uniform bound for the modified Bessel function of imaginary order.**  For `x ≥ 1` and
`τ ≥ 1`, `‖K_x(iτ)‖ ≤ e·(log(πτ) + 1)·exp(−πτ/2)`. -/
theorem norm_modifiedBesselKOrder_I_mul_le {x τ : ℝ} (hx : 1 ≤ x) (hτ : 1 ≤ τ) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      Real.exp 1 * (Real.log (Real.pi * τ) + 1) * Real.exp (-(Real.pi * τ) / 2) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hτ0 : 0 < τ := by linarith
  have hx0 : 0 < x := by linarith
  set θ : ℝ := Real.pi / 2 - 1 / τ with hθdef
  have h1τ : 1 / τ ≤ 1 := by rw [div_le_one hτ0]; exact hτ
  have h1τ0 : 0 < 1 / τ := by positivity
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
  have hθ : θ < Real.pi / 2 := by rw [hθdef]; linarith
  have hcosθ : Real.cos θ = Real.sin (1 / τ) := by rw [hθdef, Real.cos_pi_div_two_sub]
  have hsin : 2 / Real.pi * (1 / τ) ≤ Real.sin (1 / τ) :=
    Real.mul_le_sin h1τ0.le (by linarith)
  have hsin0 : 0 ≤ Real.sin (1 / τ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h1τ0.le (by linarith)
  have hbase := norm_modifiedBesselKOrder_I_mul_le_shifted hx0 τ hθ0 hθ
  set y₀ : ℝ := 2 / (Real.pi * τ) with hy₀
  have hy₀0 : 0 < y₀ := by positivity
  have hy₀2 : y₀ ≤ 2 := by
    rw [hy₀, div_le_iff₀ (by positivity)]
    nlinarith
  have hxcos : y₀ ≤ x * Real.cos θ := by
    rw [hcosθ, hy₀]
    calc 2 / (Real.pi * τ) = 2 / Real.pi * (1 / τ) := by field_simp
      _ ≤ Real.sin (1 / τ) := hsin
      _ ≤ x * Real.sin (1 / τ) := by nlinarith
  have hxcos0 : 0 < x * Real.cos θ := lt_of_lt_of_le hy₀0 hxcos
  have hint_le : (∫ t in Ioi (0 : ℝ), Real.exp (-(x * Real.cos θ) * Real.cosh t)) ≤
      ∫ t in Ioi (0 : ℝ), Real.exp (-y₀ * Real.cosh t) := by
    refine setIntegral_mono_on (integrableOn_exp_neg_mul_cosh_Ioi hxcos0)
      (integrableOn_exp_neg_mul_cosh_Ioi hy₀0) measurableSet_Ioi (fun t _ => ?_)
    apply Real.exp_le_exp.mpr
    have := Real.cosh_pos t
    nlinarith
  have htail := integral_exp_neg_mul_cosh_le hy₀0 hy₀2
  have hlog : 2 / y₀ = Real.pi * τ := by
    rw [hy₀]
    field_simp
  rw [hlog] at htail
  have hexpθ : Real.exp (-τ * θ) = Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hθdef]
    field_simp
    ring
  calc ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖
      ≤ Real.exp (-τ * θ) * ∫ t in Ioi (0 : ℝ), Real.exp (-(x * Real.cos θ) * Real.cosh t) := hbase
    _ ≤ Real.exp (-τ * θ) * (Real.log (Real.pi * τ) + 1) :=
        mul_le_mul_of_nonneg_left (hint_le.trans htail) (Real.exp_pos _).le
    _ = Real.exp 1 * (Real.log (Real.pi * τ) + 1) * Real.exp (-(Real.pi * τ) / 2) := by
        rw [hexpθ]
        ring

end

end GaloisForLFunctions.RHTower
