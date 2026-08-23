import GaloisForLFunctions.HTGeometry.ConductorHankelBound

/-!
# Integrating the resolvent family produces the conductor kernel inside a form

The conductor kernel arises as the `λ`-integral of the rank-one resolvent kernels
`e^{-(λ+2)(u+v)}`.  Inside a sesquilinear form against a bounded weight on a bounded window the
interchange is legitimate, so the `λ`-integral of the rank-one forms is the form of the conductor
kernel.

The window is bounded, but the kernel is not: `1/(u+v)` is unbounded at the corner.  Its integral
over a square is finite, which is what makes the dominated interchange work.
-/

open MeasureTheory Set Filter Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The bare conductor kernel `e^{-2r}/r`. -/
def conductorKernelBase (r : ℝ) : ℝ := Real.exp (-2 * r) / r

theorem conductorHankelKernel_eq (r : ℝ) :
    conductorHankelKernel r = 2 * Real.pi * conductorKernelBase r := by
  rw [conductorHankelKernel, conductorKernelBase]
  ring

theorem conductorKernelBase_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ conductorKernelBase r := by
  rw [conductorKernelBase]
  positivity

theorem conductorKernelBase_le {r : ℝ} (hr : 0 < r) : conductorKernelBase r ≤ 1 / r := by
  rw [conductorKernelBase, div_le_div_iff₀ hr hr]
  have hexp : Real.exp (-2 * r) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    linarith
  nlinarith

/-- **The `λ`-integral of the rank-one kernels is the conductor kernel.** -/
theorem integral_lam_rankOne {r : ℝ} (hr : 0 < r) :
    (∫ lam in Ioi (0:ℝ), Real.exp (-(lam + 2) * r)) = conductorKernelBase r := by
  have h := integral_resolventHankel hr
  have hconst : (∫ lam in Ioi (0:ℝ), 2 * Real.pi * Real.exp (-(lam + 2) * r))
      = 2 * Real.pi * ∫ lam in Ioi (0:ℝ), Real.exp (-(lam + 2) * r) :=
    MeasureTheory.integral_const_mul _ _
  rw [hconst, conductorHankelKernel_eq] at h
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi h

theorem integrableOn_rankOne {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun m : ℝ => Real.exp (-(m + 2) * r)) (Ioi 0) volume := by
  refine integrableOn_Ioi_deriv_of_nonneg
    (g := fun m : ℝ => -(1 / r) * Real.exp (-(m + 2) * r)) (l := 0) ?_ ?_
    (fun m _ => (Real.exp_pos _).le) ?_
  · refine ContinuousAt.continuousWithinAt ?_
    exact (Real.continuous_exp.continuousAt.comp
      (((continuous_id.add continuous_const).neg.mul continuous_const).continuousAt)).const_mul _
  · intro m _
    have hinner : HasDerivAt (fun t : ℝ => -(t + 2) * r) (-r) m := by
      have h := ((hasDerivAt_id m).add_const (2 : ℝ)).neg.mul_const r
      refine h.congr_deriv ?_
      ring
    have h := (Real.hasDerivAt_exp (-(m + 2) * r)).comp m hinner
    have h2 := h.const_mul (-(1 / r))
    refine h2.congr_deriv ?_
    field_simp
  · have hexp : Tendsto (fun m : ℝ => Real.exp (-(m + 2) * r)) atTop (𝓝 0) := by
      have harg : Tendsto (fun m : ℝ => -(m + 2) * r) atTop atBot := by
        have hb : Tendsto (fun m : ℝ => -(m + 2)) atTop atBot := by
          have := tendsto_neg_atTop_atBot.comp
            (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_id)
          simpa [Function.comp_def] using this
        exact hb.atBot_mul_const hr
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp harg
    simpa using hexp.const_mul (-(1 / r))

theorem lintegral_lam_rankOne {r : ℝ} (hr : 0 < r) :
    (∫⁻ lam in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(lam + 2) * r)))
      = ENNReal.ofReal (conductorKernelBase r) := by
  rw [← integral_lam_rankOne hr,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_rankOne hr)]
  filter_upwards with m
  exact (Real.exp_pos _).le

/-- **The interchange.**  Integrating the rank-one family in `λ` inside a nonnegative form gives
the conductor kernel form. -/
theorem lintegral_rankOne_swap {W : ℝ → ℝ≥0∞} (hW : Measurable W) :
    (∫⁻ lam in Ioi (0:ℝ),
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(lam + 2) * r)) * W r)
      = ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (conductorKernelBase r) * W r := by
  have hmeas : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(p.1 + 2) * p.2)) * W p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Measurable.aemeasurable (Measurable.mul ?_ (hW.comp measurable_snd))
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_fst.add measurable_const).neg.mul measurable_snd))
  rw [lintegral_lintegral_swap hmeas]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hm : Measurable fun lam : ℝ => ENNReal.ofReal (Real.exp (-(lam + 2) * r)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_id.add measurable_const).neg.mul measurable_const))
  rw [lintegral_mul_const (W r) hm, lintegral_lam_rankOne hr0]

end

end GaloisForLFunctions.HTGeometry
