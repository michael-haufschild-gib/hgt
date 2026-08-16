import GaloisForLFunctions.RHTower.ComplexLaplaceHolomorphy

/-!
# The Laplace transform of a bounded piece of the line is entire

Cutting a profile at a finite height leaves a head whose transform converges for every complex
exponent: the integrand is continuous on a bounded interval and its derivative is dominated there by
a constant.  So the head contributes no singularity, and the tail transform has exactly the
singularities of the whole.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The transform of the head of a profile. -/
def headLaplace (g : ℝ → ℝ) (H : ℝ) (s : ℂ) : ℂ :=
  ∫ L in Ioc (0 : ℝ) H, ((g L : ℝ) : ℂ) * Complex.exp (-s * ((L : ℝ) : ℂ))

set_option maxHeartbeats 1000000 in
/-- **The head transform is entire.** -/
theorem differentiable_headLaplace {g : ℝ → ℝ} (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H) :
    Differentiable ℂ (headLaplace g H) := by
  intro s₀
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := H)).exists_bound_of_continuousOn
    hg.continuousOn
  have hM0 : 0 ≤ M := by
    rcases le_or_gt 0 M with h | h
    · exact h
    · have := hM 0 ⟨le_rfl, hH⟩
      have h0 : (0:ℝ) ≤ ‖g 0‖ := norm_nonneg _
      linarith
  set C : ℝ := M * (H + 1) * Real.exp ((|s₀.re| + 1) * H) with hCdef
  have hbound : IntegrableOn (fun _ : ℝ => C) (Ioc (0 : ℝ) H) := by
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) H)) := by
      constructor
      simp [Real.volume_Ioc]
    exact integrable_const _
  have hmeasF : ∀ᶠ x : ℂ in nhds s₀,
      AEStronglyMeasurable (fun L : ℝ => ((g L : ℝ) : ℂ) * Complex.exp (-x * ((L : ℝ) : ℂ)))
        (volume.restrict (Ioc (0 : ℝ) H)) := by
    filter_upwards with x
    exact ((Complex.continuous_ofReal.comp hg).mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  have hInt : Integrable (fun L : ℝ => ((g L : ℝ) : ℂ) * Complex.exp (-s₀ * ((L : ℝ) : ℂ)))
      (volume.restrict (Ioc (0 : ℝ) H)) := by
    refine Integrable.mono' hbound ?_ ?_
    · exact ((Complex.continuous_ofReal.comp hg).mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
      have hL0 : (0 : ℝ) < L := hL.1
      have hLH : L ≤ H := hL.2
      have hgb : |g L| ≤ M := by
        have := hM L ⟨hL0.le, hLH⟩
        rwa [Real.norm_eq_abs] at this
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_mul]
      have hexp : Real.exp (-s₀.re * L) ≤ Real.exp ((|s₀.re| + 1) * H) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [abs_nonneg s₀.re, le_abs_self s₀.re, neg_abs_le s₀.re, hL0.le, hLH]
      calc |g L| * Real.exp (-s₀.re * L)
          ≤ M * Real.exp ((|s₀.re| + 1) * H) := mul_le_mul hgb hexp (Real.exp_pos _).le hM0
        _ ≤ C := by
            rw [hCdef]
            nlinarith [mul_nonneg (mul_nonneg hM0 (Real.exp_pos ((|s₀.re| + 1) * H)).le) hH]
  have hmeasF' : AEStronglyMeasurable
      (fun L : ℝ => -(((L : ℝ) : ℂ) * (((g L : ℝ) : ℂ) * Complex.exp (-s₀ * ((L : ℝ) : ℂ)))))
      (volume.restrict (Ioc (0 : ℝ) H)) :=
    ((Complex.continuous_ofReal.mul ((Complex.continuous_ofReal.comp hg).mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)))).neg).aestronglyMeasurable
  have hdom : ∀ᵐ L : ℝ ∂(volume.restrict (Ioc (0 : ℝ) H)), ∀ x ∈ Metric.ball s₀ 1,
      ‖-(((L : ℝ) : ℂ) * (((g L : ℝ) : ℂ) * Complex.exp (-x * ((L : ℝ) : ℂ))))‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL x hx
    have hL0 : (0 : ℝ) < L := hL.1
    have hLH : L ≤ H := hL.2
    have hgb : |g L| ≤ M := by
      have := hM L ⟨hL0.le, hLH⟩
      rwa [Real.norm_eq_abs] at this
    have hxre : s₀.re - 1 < x.re := by
      have h1 : |x.re - s₀.re| ≤ ‖x - s₀‖ := by
        have := Complex.abs_re_le_norm (x - s₀)
        simpa using this
      have h2 : ‖x - s₀‖ < 1 := by
        rw [← Complex.dist_eq]
        exact Metric.mem_ball.mp hx
      have := abs_lt.mp (lt_of_le_of_lt h1 h2)
      linarith [this.1]
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, norm_cexp_neg_mul, abs_of_pos hL0]
    have hexp : Real.exp (-x.re * L) ≤ Real.exp ((|s₀.re| + 1) * H) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [abs_nonneg s₀.re, le_abs_self s₀.re, neg_abs_le s₀.re, hL0.le, hLH, hxre]
    calc L * (|g L| * Real.exp (-x.re * L))
        ≤ H * (M * Real.exp ((|s₀.re| + 1) * H)) := by
          refine mul_le_mul hLH ?_ (by positivity) (by linarith)
          exact mul_le_mul hgb hexp (Real.exp_pos _).le hM0
      _ ≤ C := by
          rw [hCdef]
          nlinarith [mul_nonneg hM0 (Real.exp_pos ((|s₀.re| + 1) * H)).le]
  have hderiv : ∀ᵐ L : ℝ ∂(volume.restrict (Ioc (0 : ℝ) H)), ∀ x ∈ Metric.ball s₀ 1,
      HasDerivAt (fun y : ℂ => ((g L : ℝ) : ℂ) * Complex.exp (-y * ((L : ℝ) : ℂ)))
        (-(((L : ℝ) : ℂ) * (((g L : ℝ) : ℂ) * Complex.exp (-x * ((L : ℝ) : ℂ))))) x := by
    filter_upwards with L x _
    have h1 : HasDerivAt (fun y : ℂ => -y * ((L : ℝ) : ℂ)) (-((L : ℝ) : ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℂ => (-((L : ℝ) : ℂ)) * y) ((-((L : ℝ) : ℂ)) * 1) x :=
        (hasDerivAt_id x).const_mul (-((L : ℝ) : ℂ))
      refine h0.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
      filter_upwards with y
      ring
    have h2 := (h1.cexp).const_mul (((g L : ℝ) : ℂ))
    refine h2.congr_deriv ?_
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (L : ℝ) => ((g L : ℝ) : ℂ) * Complex.exp (-x * ((L : ℝ) : ℂ)))
    (F' := fun (x : ℂ) (L : ℝ) =>
      -(((L : ℝ) : ℂ) * (((g L : ℝ) : ℂ) * Complex.exp (-x * ((L : ℝ) : ℂ)))))
    (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds s₀ one_pos) hmeasF hInt hmeasF' hdom hbound hderiv
  exact (hmain.2).differentiableAt

end GaloisForLFunctions.RHTower
