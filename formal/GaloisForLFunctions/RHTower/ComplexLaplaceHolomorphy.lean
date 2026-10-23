import GaloisForLFunctions.RHTower.LaplaceTransformMomentDerivative

/-!
# The complex Laplace transform is holomorphic right of the abscissa

The same domination that proves the real transform differentiable proves the complex one
holomorphic: on a ball strictly inside the half-plane every kernel derivative is bounded by
`u e^{-bu}` with `b` still right of the abscissa, and that majorant is integrable.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The complex Laplace transform of a measure on the positive ray. -/
def complexLaplace (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) ∂ν

theorem integrable_cexp_of_gt_abscissa {ν : Measure ℝ} {c : ℝ} (hc : IsAbscissa ν c) {z : ℂ}
    (hz : c < z.re) :
    Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ))) := by
  have hreal : Integrable (fun u : ℝ => Real.exp (-z.re * u)) (ν.restrict (Ioi (0 : ℝ))) :=
    integrableOn_exp_neg_of_gt_abscissa hc hz
  refine Integrable.mono' hreal ?_ ?_
  · exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  · filter_upwards with u
    exact le_of_eq (norm_cexp_neg_mul z u)

theorem integrable_id_mul_cexp_of_gt_abscissa {ν : Measure ℝ} {c b : ℝ} (hc : IsAbscissa ν c)
    (hb : c < b) {z : ℂ} (hzb : b ≤ z.re) :
    Integrable (fun u : ℝ => (u : ℂ) * Complex.exp (-z * (u : ℂ)))
      (ν.restrict (Ioi (0 : ℝ))) := by
  have hreal : Integrable (fun u : ℝ => u * Real.exp (-b * u)) (ν.restrict (Ioi (0 : ℝ))) :=
    integrableOn_mul_exp_neg_of_gt_abscissa hc hb
  refine Integrable.mono' hreal ?_ ?_
  · exact (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0, norm_cexp_neg_mul]
    refine mul_le_mul_of_nonneg_left ?_ hu0
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hu0, hzb]

/-- **The complex transform is differentiable right of the abscissa.** -/
theorem hasDerivAt_complexLaplace {ν : Measure ℝ} {c : ℝ} (hc : IsAbscissa ν c) {z : ℂ}
    (hz : c < z.re) :
    HasDerivAt (complexLaplace ν)
      (∫ u in Ioi (0 : ℝ), -((u : ℂ) * Complex.exp (-z * (u : ℂ))) ∂ν) z := by
  set ε : ℝ := (z.re - c) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hlow : c < z.re - ε := by rw [hε]; linarith
  have hbound : Integrable (fun u : ℝ => u * Real.exp (-(z.re - ε) * u))
      (ν.restrict (Ioi (0 : ℝ))) := integrableOn_mul_exp_neg_of_gt_abscissa hc hlow
  have hmeasF : ∀ᶠ x : ℂ in nhds z,
      AEStronglyMeasurable (fun u : ℝ => Complex.exp (-x * (u : ℂ)))
        (ν.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with x
    exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have hInt := integrable_cexp_of_gt_abscissa hc hz
  have hmeasF' : AEStronglyMeasurable (fun u : ℝ => -((u : ℂ) * Complex.exp (-z * (u : ℂ))))
      (ν.restrict (Ioi (0 : ℝ))) :=
    ((Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).neg).aestronglyMeasurable
  have hdom : ∀ᵐ u : ℝ ∂(ν.restrict (Ioi (0 : ℝ))), ∀ x ∈ Metric.ball z ε,
      ‖-((u : ℂ) * Complex.exp (-x * (u : ℂ)))‖ ≤ u * Real.exp (-(z.re - ε) * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x hx
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hxre : z.re - ε < x.re := by
      have h1 : |x.re - z.re| ≤ ‖x - z‖ := by
        have := Complex.abs_re_le_norm (x - z)
        simpa using this
      have h2 : ‖x - z‖ < ε := by
        rw [← Complex.dist_eq]
        exact Metric.mem_ball.mp hx
      have h3 : |x.re - z.re| < ε := lt_of_le_of_lt h1 h2
      have := abs_lt.mp h3
      linarith [this.1]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0, norm_cexp_neg_mul]
    refine mul_le_mul_of_nonneg_left ?_ hu0
    refine Real.exp_le_exp.mpr ?_
    linarith [mul_le_mul_of_nonneg_right hxre.le hu0]
  have hderiv : ∀ᵐ u : ℝ ∂(ν.restrict (Ioi (0 : ℝ))), ∀ x ∈ Metric.ball z ε,
      HasDerivAt (fun y : ℂ => Complex.exp (-y * (u : ℂ)))
        (-((u : ℂ) * Complex.exp (-x * (u : ℂ)))) x := by
    filter_upwards with u x _
    have h1 : HasDerivAt (fun y : ℂ => -y * (u : ℂ)) (-(u : ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℂ => (-(u : ℂ)) * y) ((-(u : ℂ)) * 1) x :=
        (hasDerivAt_id x).const_mul (-(u : ℂ))
      refine h0.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
      filter_upwards with y
      ring
    have h2 := h1.cexp
    refine h2.congr_deriv ?_
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (u : ℝ) => Complex.exp (-x * (u : ℂ)))
    (F' := fun (x : ℂ) (u : ℝ) => -((u : ℂ) * Complex.exp (-x * (u : ℂ))))
    (bound := fun u : ℝ => u * Real.exp (-(z.re - ε) * u))
    (Metric.ball_mem_nhds z hε0) hmeasF hInt hmeasF' hdom hbound hderiv
  exact hmain.2

/-- **The complex transform is holomorphic right of the abscissa.** -/
theorem differentiableOn_complexLaplace {ν : Measure ℝ} {c : ℝ} (hc : IsAbscissa ν c) :
    DifferentiableOn ℂ (complexLaplace ν) {z : ℂ | c < z.re} := by
  intro z hz
  exact ((hasDerivAt_complexLaplace hc hz).differentiableAt).differentiableWithinAt

end GaloisForLFunctions.RHTower
