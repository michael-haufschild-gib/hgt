import GaloisForLFunctions.HTGeometry.IntegralCesaro

/-!
# Logarithmic Cesàro asymptotics

If `u · f(u)` converges at infinity then the primitive of `f` grows logarithmically with exactly
that constant:

`(∫₁^R f)/log R → c`.

The exponential substitution `u = e^t` turns the logarithmic average into the ordinary one, so this
is the corpus's `tendsto_intervalAverage_atTop_of_tendsto` transported along `exp`.
-/

open Filter Topology intervalIntegral MeasureTheory Set

namespace HTGeometry

theorem tendsto_logInv_atTop : Tendsto (fun q : ℝ => Real.log (1 / q)) (𝓝[>] (0 : ℝ)) atTop := by
  have h : Tendsto (fun q : ℝ => 1 / q) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  exact Real.tendsto_log_atTop.comp h

/-- **The logarithmic Cesàro theorem.** -/
theorem tendsto_logAverage_atTop_of_tendsto {f : ℝ → ℝ} (hcont : Continuous f) {c : ℝ}
    (h : Tendsto (fun u : ℝ => u * f u) atTop (𝓝 c)) :
    Tendsto (fun R : ℝ => (∫ u in (1 : ℝ)..R, f u) / Real.log R) atTop (𝓝 c) := by
  set φ : ℝ → ℝ := fun t => Real.exp t * f (Real.exp t) with hφ
  have hφcont : Continuous φ := by
    rw [hφ]
    exact Real.continuous_exp.mul (hcont.comp Real.continuous_exp)
  have hφlim : Tendsto φ atTop (𝓝 c) := h.comp Real.tendsto_exp_atTop
  have havg := tendsto_intervalAverage_atTop_of_tendsto hφcont hφlim 0
  have hsub : ∀ S : ℝ, (∫ t in (0 : ℝ)..S, φ t) = ∫ u in (1 : ℝ)..Real.exp S, f u := by
    intro S
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) S, HasDerivAt Real.exp (Real.exp x) x :=
      fun x _ => Real.hasDerivAt_exp x
    have := intervalIntegral.integral_deriv_smul_comp (a := (0 : ℝ)) (b := S)
      (f := Real.exp) (f' := Real.exp) (g := f) hderiv
      (Real.continuous_exp.continuousOn) hcont
    rw [Real.exp_zero] at this
    simpa [hφ, Function.comp_def, smul_eq_mul] using this
  have hcomp := havg.comp Real.tendsto_log_atTop
  refine Tendsto.congr' ?_ hcomp
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Function.comp_apply, hsub, Real.exp_log hR, sub_zero]

end HTGeometry
