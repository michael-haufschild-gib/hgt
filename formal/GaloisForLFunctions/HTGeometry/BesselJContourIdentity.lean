import GaloisForLFunctions.HTGeometry.BesselJGeneratingFunction

/-!
# A contour identity for odd-order Bessel functions

For odd `l ≥ 1` and `x ≥ 0`, Cauchy's theorem for the entire function `θ ↦ e^{i(lθ + x sin θ)}` on the
rectangles `[0, π/2] × [0, T]` (the top edge is `O(e^{−lT})`, the left edge is real) gives

`∫_0^{π/2} cos(lθ + x sin θ) dθ = sin(lπ/2) ∫_0^∞ e^{−lw} cos(x cosh w) dw`

(`integral_cos_add_sin_eq`).  Integrating by parts on both pieces and using Bessel's integral
`J_l(x) = (2/π)∫_0^{π/2} sin(lθ) sin(x sin θ) dθ`, for odd `l ≥ 3` and `x > 0`:

`∫_0^{π/2} sin(lθ) sin(x sin θ) cos θ dθ + sin(lπ/2) ∫_0^∞ sinh w e^{−lw} sin(x cosh w) dw = (πl/2) J_l(x)/x`

(`integral_sine_profile_eq`): the sine transform of `u ↦ sin(l arcsin u)` (`u ≤ 1`),
`sin(lπ/2)(u − √(u²−1))^l` (`u ≥ 1`) is `(πl/2) J_l(x)/x`, written in the variables `u = sin θ`, `u = cosh w`.
-/

open MeasureTheory Set Filter Topology Complex intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The integrand `e^{i(lθ + x sin θ)}`. -/
def besselContourFun (l : ℕ) (x : ℝ) (θ : ℂ) : ℂ :=
  cexp (Complex.I * ((l : ℂ) * θ + x * Complex.sin θ))

theorem differentiable_besselContourFun (l : ℕ) (x : ℝ) : Differentiable ℂ (besselContourFun l x) := by
  unfold besselContourFun; fun_prop

theorem besselContourFun_right (l : ℕ) (x y : ℝ) :
    besselContourFun l x (((Real.pi / 2 : ℝ) : ℂ) + y * Complex.I) =
      cexp (Complex.I * ((l * (Real.pi / 2) : ℝ) : ℂ)) *
        (Real.exp (-(l * y)) * cexp (Complex.I * (x * Real.cosh y))) := by
  unfold besselContourFun
  have hs : Complex.sin (((Real.pi / 2 : ℝ) : ℂ) + y * Complex.I) = Real.cosh y := by
    rw [Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, Real.sin_pi_div_two, Real.cos_pi_div_two, Complex.ofReal_cosh]
    simp
  have e : Complex.I * ((l : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) + y * Complex.I) + x * (Real.cosh y : ℂ)) =
      Complex.I * ((l * (Real.pi / 2) : ℝ) : ℂ) + ((-(l * y) : ℝ) : ℂ) +
        Complex.I * (x * Real.cosh y) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hs, e, Complex.exp_add, Complex.exp_add, Complex.ofReal_exp]
  ring

theorem re_I_mul_cexp_I_mul (a : ℝ) : (Complex.I * cexp (Complex.I * a)).re = -Real.sin a := by
  rw [mul_comm Complex.I (a : ℂ), Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]

theorem im_I_mul_cexp_I_mul (a : ℝ) : (Complex.I * cexp (Complex.I * a)).im = Real.cos a := by
  rw [mul_comm Complex.I (a : ℂ), Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]

theorem besselContourFun_left (l : ℕ) (x y : ℝ) :
    besselContourFun l x (((0 : ℝ) : ℂ) + y * Complex.I) = ((Real.exp (-(l * y) - x * Real.sinh y) : ℝ) : ℂ) := by
  unfold besselContourFun
  rw [Complex.ofReal_zero, zero_add, Complex.sin_mul_I, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_besselContourFun_top {l : ℕ} {x : ℝ} (hx : 0 ≤ x) {σ : ℝ} (hσ : σ ∈ uIcc 0 (Real.pi / 2))
    (T : ℝ) (hT : 0 ≤ T) :
    ‖besselContourFun l x ((σ : ℂ) + T * Complex.I)‖ ≤ Real.exp (-(l * T)) := by
  unfold besselContourFun
  rw [Complex.norm_exp, Real.exp_le_exp]
  rw [uIcc_of_le (by positivity)] at hσ
  have hc : 0 ≤ Real.cos σ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hσ.1, Real.pi_pos], hσ.2.trans
    (le_refl _)⟩
  have hsh : 0 ≤ Real.sinh T := Real.sinh_nonneg_iff.2 hT
  have hre : (Complex.I * ((l : ℂ) * ((σ : ℂ) + T * Complex.I) + x * Complex.sin ((σ : ℂ) + T * Complex.I))).re =
      -(l * T) - x * (Real.cos σ * Real.sinh T) := by
    rw [Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hre]
  nlinarith [mul_nonneg hx (mul_nonneg hc hsh)]

theorem integrableOn_exp_neg_mul_cos_cosh {l : ℕ} (hl : 1 ≤ l) (x : ℝ) :
    IntegrableOn (fun w : ℝ => Real.exp (-(l * w)) * Real.cos (x * Real.cosh w)) (Ioi 0) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  refine (exp_neg_integrableOn_Ioi 0 hl0).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w _ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), show -(l * w) = -(l : ℝ) * w by ring]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- **The contour identity**: `∫_0^{π/2} cos(lθ + x sin θ) dθ = sin(lπ/2) ∫_0^∞ e^{−lw} cos(x cosh w) dw`,
odd `l ≥ 1`, `x ≥ 0`. -/
theorem integral_cos_add_sin_eq {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos ((2 * k + 1 : ℕ) * θ + x * Real.sin θ) =
      Real.sin ((2 * k + 1 : ℕ) * (Real.pi / 2)) *
        ∫ w in Ioi (0 : ℝ), Real.exp (-((2 * k + 1 : ℕ) * w)) * Real.cos (x * Real.cosh w) := by
  set l : ℕ := 2 * k + 1
  have hl : 1 ≤ l := by omega
  set f := besselContourFun l x
  -- Cauchy on `[0, π/2] × [0, T]`
  have hrect : ∀ T : ℝ, 0 ≤ T →
      (∫ σ in (0 : ℝ)..Real.pi / 2, f σ) - (∫ σ in (0 : ℝ)..Real.pi / 2, f ((σ : ℂ) + T * Complex.I)) +
        Complex.I • (∫ y in (0 : ℝ)..T, f (((Real.pi / 2 : ℝ) : ℂ) + y * Complex.I)) -
        Complex.I • (∫ y in (0 : ℝ)..T, f (((0 : ℝ) : ℂ) + y * Complex.I)) = 0 := fun T hT => by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f 0
      (((Real.pi / 2 : ℝ) : ℂ) + T * Complex.I) (differentiable_besselContourFun l x).differentiableOn
    simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im] at h
    simpa using h
  -- real parts
  have hbot : (∫ σ in (0 : ℝ)..Real.pi / 2, f σ).re =
      ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (l * θ + x * Real.sin θ) := by
    have hint : IntervalIntegrable (fun σ : ℝ => f σ) volume 0 (Real.pi / 2) :=
      Continuous.intervalIntegrable ((differentiable_besselContourFun l x).continuous.comp
        Complex.continuous_ofReal) _ _
    have hc := Complex.reCLM.intervalIntegral_comp_comm hint
    rw [← Complex.reCLM_apply, ← hc]
    congr 1; funext θ
    rw [Complex.reCLM_apply]
    simp only [f, besselContourFun]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_sin, show Complex.I * (((l : ℝ) : ℂ) * (θ : ℂ) +
      (x : ℂ) * ((Real.sin θ : ℝ) : ℂ)) = ((l * θ + x * Real.sin θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hright : ∀ T : ℝ, (Complex.I • ∫ y in (0 : ℝ)..T, f (((Real.pi / 2 : ℝ) : ℂ) + y * Complex.I)).re =
      -Real.sin (l * (Real.pi / 2)) * ∫ y in (0 : ℝ)..T, Real.exp (-(l * y)) * Real.cos (x * Real.cosh y) := by
    intro T
    simp_rw [f, besselContourFun_right, smul_eq_mul, intervalIntegral.integral_const_mul, ← mul_assoc]
    rw [Complex.mul_re, re_I_mul_cexp_I_mul, im_I_mul_cexp_I_mul]
    have hc : Real.cos (l * (Real.pi / 2)) = 0 := by
      rw [show (l : ℝ) * (Real.pi / 2) = (k : ℝ) * Real.pi + Real.pi / 2 by simp [l]; ring,
        Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
    rw [hc, zero_mul, sub_zero]
    congr 1
    have hint : IntervalIntegrable (fun y : ℝ => ((Real.exp (-(l * y)) : ℝ) : ℂ) *
        cexp (Complex.I * x * Real.cosh y)) volume 0 T :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have hc := Complex.reCLM.intervalIntegral_comp_comm hint
    rw [← Complex.reCLM_apply, ← hc]
    congr 1; funext y
    rw [Complex.reCLM_apply]
    rw [Complex.re_ofReal_mul, show Complex.I * (x : ℂ) * ((Real.cosh y : ℝ) : ℂ) =
      ((x * Real.cosh y : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
  have hleft : ∀ T : ℝ, (Complex.I • ∫ y in (0 : ℝ)..T, f (((0 : ℝ) : ℂ) + y * Complex.I)).re = 0 := by
    intro T
    simp_rw [f, besselContourFun_left, smul_eq_mul, intervalIntegral.integral_ofReal]
    simp
  -- the limit `T → ∞`
  have htop : Tendsto (fun T : ℝ => (∫ σ in (0 : ℝ)..Real.pi / 2, f ((σ : ℂ) + T * Complex.I)).re)
      atTop (𝓝 0) := by
    have hb : ∀ᶠ T : ℝ in atTop, ‖(∫ σ in (0 : ℝ)..Real.pi / 2, f ((σ : ℂ) + T * Complex.I)).re‖ ≤
        Real.pi / 2 * Real.exp (-(l * T)) := by
      filter_upwards [eventually_ge_atTop 0] with T hT
      refine (Complex.abs_re_le_norm _).trans ?_
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ =>
        norm_besselContourFun_top hx (uIoc_subset_uIcc hσ) T hT).trans (le_of_eq ?_)
      rw [sub_zero, abs_of_pos (by positivity)]; ring
    refine squeeze_zero_norm' hb ?_
    have : Tendsto (fun T : ℝ => Real.exp (-(l * T))) atTop (𝓝 0) := by
      have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hl0 tendsto_id)
    simpa using this.const_mul (Real.pi / 2)
  have hR : Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..T, Real.exp (-(l * y)) * Real.cos (x * Real.cosh y))
      atTop (𝓝 (∫ w in Ioi (0 : ℝ), Real.exp (-(l * w)) * Real.cos (x * Real.cosh w))) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_neg_mul_cos_cosh hl x) tendsto_id
  have hEq : ∀ᶠ T : ℝ in atTop, ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (l * θ + x * Real.sin θ) =
      (∫ σ in (0 : ℝ)..Real.pi / 2, f ((σ : ℂ) + T * Complex.I)).re +
        Real.sin (l * (Real.pi / 2)) * ∫ y in (0 : ℝ)..T, Real.exp (-(l * y)) * Real.cos (x * Real.cosh y) := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    have h := congrArg Complex.re (hrect T hT)
    simp only [Complex.sub_re, Complex.add_re, Complex.zero_re] at h
    rw [hbot, hright T, hleft T] at h
    linarith
  have hlim := (htop.add (hR.const_mul (Real.sin (l * (Real.pi / 2))))).congr'
    (hEq.mono fun T h => h.symm)
  rw [zero_add] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim)


/-! ## The sine profile of `J_l(x)/x` -/

theorem integrableOn_sinh_mul_exp_neg {l : ℕ} (hl : 3 ≤ l) :
    IntegrableOn (fun w : ℝ => Real.exp (-(l * w)) * Real.sinh w) (Ioi 0) := by
  have h2 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  refine (exp_neg_integrableOn_Ioi 0 h2).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
  have hw0 : (0 : ℝ) < w := hw
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sinh_nonneg_iff.2 hw0.le)]
  calc Real.exp (-(l * w)) * Real.sinh w ≤ Real.exp (-(l * w)) * Real.exp w := by
        gcongr; rw [Real.sinh_eq]; linarith [Real.exp_pos (-w), Real.exp_pos w]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem integral_sine_part_eq {l : ℕ} {x : ℝ} (hx : x ≠ 0) :
    ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin (l * θ) * (Real.sin (x * Real.sin θ) * Real.cos θ) =
      -(Real.sin (l * (Real.pi / 2)) * Real.cos x / x) +
        (l / x) * ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (l * θ) * Real.cos (x * Real.sin θ) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := Real.pi / 2)
    (u := fun θ : ℝ => Real.sin (l * θ)) (u' := fun θ => l * Real.cos (l * θ))
    (v := fun θ : ℝ => -Real.cos (x * Real.sin θ) / x)
    (v' := fun θ => Real.sin (x * Real.sin θ) * Real.cos θ)
    (fun θ _ => (((hasDerivAt_id' θ).const_mul (l : ℝ)).sin).congr_deriv (by ring))
    (fun θ _ => ((((Real.hasDerivAt_sin θ).const_mul x).cos.neg).div_const x).congr_deriv (by
      field_simp))
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [h, Real.sin_pi_div_two, mul_one, mul_zero, Real.sin_zero, zero_mul, sub_zero]
  have : ∫ θ in (0 : ℝ)..Real.pi / 2, l * Real.cos (l * θ) * (-Real.cos (x * Real.sin θ) / x) =
      -((l / x) * ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (l * θ) * Real.cos (x * Real.sin θ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext θ; ring
  rw [this]; ring

theorem integral_hyperbolic_part_eq {l : ℕ} (hl : 3 ≤ l) {x : ℝ} (hx : 0 < x) :
    ∫ w in Ioi (0 : ℝ), Real.exp (-(l * w)) * (Real.sinh w * Real.sin (x * Real.cosh w)) =
      Real.cos x / x - (l / x) * ∫ w in Ioi (0 : ℝ), Real.exp (-(l * w)) * Real.cos (x * Real.cosh w) := by
  have hl0 : (0 : ℝ) < l := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hE : Tendsto (fun w : ℝ => Real.exp (-(l * w))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hl0 tendsto_id)
  have huv' : IntegrableOn ((fun w : ℝ => Real.exp (-(l * w))) *
      fun w => Real.sinh w * Real.sin (x * Real.cosh w)) (Ioi 0) := by
    refine (integrableOn_sinh_mul_exp_neg hl).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    have hw0 : (0 : ℝ) < w := hw
    have hs := Real.sinh_nonneg_iff.2 hw0.le
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
    have h1 := Real.abs_sin_le_one (x * Real.cosh w)
    have h2 : 0 ≤ Real.exp (-(l * w)) * Real.sinh w := mul_nonneg (Real.exp_pos _).le hs
    nlinarith
  have hu'v : IntegrableOn ((fun w : ℝ => -(l : ℝ) * Real.exp (-(l * w))) *
      fun w => -Real.cos (x * Real.cosh w) / x) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hl0).const_mul ((l : ℝ) / x)).mono'
      (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun w => ?_)
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _), abs_div, abs_neg,
      abs_of_pos hx, Nat.abs_cast, show -(l * w) = -(l : ℝ) * w by ring]
    have h1 := Real.abs_cos_le_one (x * Real.cosh w)
    calc (l : ℝ) * Real.exp (-(l : ℝ) * w) * (|Real.cos (x * Real.cosh w)| / x) ≤
          (l : ℝ) * Real.exp (-(l : ℝ) * w) * (1 / x) := by gcongr
      _ = _ := by ring
  have hlim0 : Tendsto ((fun w : ℝ => Real.exp (-(l * w))) * fun w => -Real.cos (x * Real.cosh w) / x)
      (𝓝[>] 0) (𝓝 (-Real.cos x / x)) := by
    have hc : ContinuousAt (fun w : ℝ => Real.exp (-(l * w)) * (-Real.cos (x * Real.cosh w) / x)) 0 := by
      fun_prop
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simp only [mul_zero, neg_zero, Real.exp_zero, Real.cosh_zero, mul_one, one_mul] at this
    exact this
  have hlimT : Tendsto ((fun w : ℝ => Real.exp (-(l * w))) * fun w => -Real.cos (x * Real.cosh w) / x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun w => Real.exp (-(l * w)) * (1 / x)) (fun w => ?_)
      (by simpa using hE.mul_const (1 / x))
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_div, norm_neg, Real.norm_of_nonneg hx.le]
    have h1 := Real.abs_cos_le_one (x * Real.cosh w)
    rw [Real.norm_eq_abs]
    gcongr
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun w : ℝ => Real.exp (-(l * w))) (u' := fun w => -(l : ℝ) * Real.exp (-(l * w)))
    (v := fun w : ℝ => -Real.cos (x * Real.cosh w) / x)
    (v' := fun w => Real.sinh w * Real.sin (x * Real.cosh w))
    (fun w _ => by
      have h0 : HasDerivAt (fun w : ℝ => -(l * w)) (-(l : ℝ)) w := by
        have e : (fun w : ℝ => -(l * w)) = fun w => -(l : ℝ) * w := by funext w; ring
        rw [e]
        exact ((hasDerivAt_id' w).const_mul (-(l : ℝ))).congr_deriv (by ring)
      exact h0.exp.congr_deriv (by ring))
    (fun w _ => ((((Real.hasDerivAt_cosh w).const_mul x).cos.neg).div_const x).congr_deriv (by
      field_simp))
    huv' hu'v hlim0 hlimT
  rw [h]
  have : ∫ w in Ioi (0 : ℝ), -(l : ℝ) * Real.exp (-(l * w)) * (-Real.cos (x * Real.cosh w) / x) =
      (l / x) * ∫ w in Ioi (0 : ℝ), Real.exp (-(l * w)) * Real.cos (x * Real.cosh w) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; funext w; field_simp
  rw [this]; ring

/-- **The sine profile of `J_l(x)/x`**, odd `l ≥ 3`, `x > 0`. -/
theorem integral_sine_profile_eq {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) *
        (Real.sin (x * Real.sin θ) * Real.cos θ)) +
      Real.sin ((2 * k + 1 : ℕ) * (Real.pi / 2)) *
        ∫ w in Ioi (0 : ℝ), Real.exp (-((2 * k + 1 : ℕ) * w)) * (Real.sinh w * Real.sin (x * Real.cosh w)) =
      Real.pi * (2 * k + 1 : ℕ) / 2 * (besselJ (2 * k + 1) x / x) := by
  rw [integral_sine_part_eq hx.ne', integral_hyperbolic_part_eq (by omega) hx]
  have hB5 := integral_cos_add_sin_eq (k := k) hx.le
  have hBJ := besselJ_odd_eq_integral k x
  have hsplit : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos ((2 * k + 1 : ℕ) * θ + x * Real.sin θ) =
      (∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos ((2 * k + 1 : ℕ) * θ) * Real.cos (x * Real.sin θ)) -
        ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin (x * Real.sin θ) := by
    rw [← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    congr 1; funext θ; rw [Real.cos_add]
  have hJ : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin (x * Real.sin θ) =
      Real.pi / 2 * besselJ (2 * k + 1) x := by
    rw [hBJ]; field_simp
  rw [hsplit, hJ] at hB5
  rw [show Real.pi * ((2 * k + 1 : ℕ) : ℝ) / 2 * (besselJ (2 * k + 1) x / x) =
      (((2 * k + 1 : ℕ) : ℝ) / x) * (Real.pi / 2 * besselJ (2 * k + 1) x) by ring]
  rw [show Real.pi / 2 * besselJ (2 * k + 1) x =
      (∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos ((2 * k + 1 : ℕ) * θ) * Real.cos (x * Real.sin θ)) -
        Real.sin ((2 * k + 1 : ℕ) * (Real.pi / 2)) *
          ∫ w in Ioi (0 : ℝ), Real.exp (-((2 * k + 1 : ℕ) * w)) * Real.cos (x * Real.cosh w) by
    linarith [hB5]]
  ring

end

end GaloisForLFunctions.HTGeometry
