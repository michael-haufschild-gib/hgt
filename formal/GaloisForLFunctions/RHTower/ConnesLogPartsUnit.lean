import GaloisForLFunctions.RHTower.ConnesLogPartsTail

/-!
# Step 2, the unit interval: integration by parts on `(0, 1]`

Step 2 of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

On `(0, 1]` the primitive of `G'(u) log u + (G(u) − G(0))/u` is `(G(u) − G(0)) log u`, which
vanishes at `1` (`log 1 = 0`) and at `0` (`ConnesSchwartzLogDecay`).  Hence

  `∫_0^(1 : ℕ) (G'(u) log u + (G(u) − G(0))/u) du = 0`.

Subtracting `G(0)` is what makes the primitive continuous at the origin; this is the step that
removes the Euler–Mascheroni constant from the final identification.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap Interval

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The primitive on the unit interval. -/
theorem connes_hasDerivAt_sub_mul_log (G : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((Real.log u : ℝ) : ℂ))
      (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x * ((Real.log x : ℝ) : ℂ)
        + ((G : ℝ → ℂ) x - (G : ℝ → ℂ) 0) * ((x⁻¹ : ℝ) : ℂ)) x := by
  have hG : HasDerivAt (fun u : ℝ => (G : ℝ → ℂ) u - (G : ℝ → ℂ) 0)
      (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x) x :=
    ((G.differentiable.differentiableAt).hasDerivAt).sub_const _
  exact hG.mul (connes_hasDerivAt_ofReal_log hx)

/-- The primitive is continuous on `[0,1]`. -/
theorem connes_continuousOn_sub_mul_log (G : 𝓢(ℝ, ℂ)) :
    ContinuousOn (fun u : ℝ => ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((Real.log u : ℝ) : ℂ))
      (Icc (0 : ℝ) 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · have hx0 : x = 0 := h0.symm
    subst hx0
    have hval : ((G : ℝ → ℂ) 0 - (G : ℝ → ℂ) 0) * ((Real.log 0 : ℝ) : ℂ) = 0 := by
      simp
    have hIoi : ContinuousWithinAt
        (fun u : ℝ => ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((Real.log u : ℝ) : ℂ))
        (Ioi (0 : ℝ)) 0 := by
      rw [ContinuousWithinAt, hval]
      exact connes_schwartz_sub_mul_log_atZero G
    exact (continuousWithinAt_Ioi_iff_Ici.mp hIoi).mono Set.Icc_subset_Ici_self
  · refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ ?_
    · exact (G.continuous.continuousAt).sub continuousAt_const
    · exact (Complex.continuous_ofReal.continuousAt).comp
        (Real.continuousAt_log (ne_of_gt h0))

/-- The unit-interval integrand is interval integrable. -/
theorem connes_unit_integrand_intervalIntegrable (G : 𝓢(ℝ, ℂ)) :
    IntervalIntegrable (fun u : ℝ => deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
      + ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((u⁻¹ : ℝ) : ℂ)) volume 0 1 := by
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_diffQuotient_bound G
  set D : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ G with hD
  set σ : ℝ := SchwartzMap.seminorm ℂ 0 0 D with hσ
  have hσ0 : (0 : ℝ) ≤ σ := apply_nonneg _ D
  have hDb : ∀ u : ℝ, ‖deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u‖ ≤ σ := by
    intro u
    rw [connes_deriv_eq_derivCLM G u, ← hD]
    have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ D 0 u
    simpa using h0
  have hlogint : IntervalIntegrable (fun u : ℝ => Real.log u) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'
  refine IntervalIntegrable.add ?_ ?_
  · rw [intervalIntegrable_iff]
    have hlogI : IntegrableOn (fun u : ℝ => ‖Real.log u‖) (Ι (0 : ℝ) 1) volume := by
      have h := hlogint.norm
      rw [intervalIntegrable_iff] at h
      exact h
    refine Integrable.mono' (hlogI.const_mul σ) ?_ ?_
    · refine AEStronglyMeasurable.restrict ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((SchwartzMap.derivCLM ℂ ℂ G).continuous.aestronglyMeasurable).congr
          (Filter.Eventually.of_forall fun u => (connes_deriv_eq_derivCLM G u).symm)
      · exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hDb u) (abs_nonneg _)
  · rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      refine (G.continuous.measurable.sub measurable_const).mul ?_
      exact Complex.measurable_ofReal.comp measurable_inv
    · filter_upwards with u
      rcases eq_or_ne u 0 with hu | hu
      · simp [hu, hC0]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
        have h1 : ‖(G : ℝ → ℂ) u - (G : ℝ → ℂ) 0‖ * |u|⁻¹ ≤ (C * |u|) * |u|⁻¹ :=
          mul_le_mul_of_nonneg_right (hC u) (by positivity)
        have h2 : (C * |u|) * |u|⁻¹ = C := by
          field_simp
        rw [h2] at h1
        exact h1

/-- **Step 2, the unit interval.**  `∫_0^(1 : ℕ) (G'(u) log u + (G(u) − G(0))/u) du = 0`. -/
theorem connes_log_ftc_unit (G : 𝓢(ℝ, ℂ)) :
    (∫ u in (0 : ℝ)..1, (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
      + ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((u⁻¹ : ℝ) : ℂ))) = 0 := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ => ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((Real.log u : ℝ) : ℂ))
        (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x * ((Real.log x : ℝ) : ℂ)
          + ((G : ℝ → ℂ) x - (G : ℝ → ℂ) 0) * ((x⁻¹ : ℝ) : ℂ)) (Ioi x) x := by
    intro x hx
    exact (connes_hasDerivAt_sub_mul_log G (ne_of_gt hx.1)).hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num : (0 : ℝ) ≤ 1)
    (connes_continuousOn_sub_mul_log G) hderiv (connes_unit_integrand_intervalIntegrable G)
  rw [h]
  simp

end

end GaloisForLFunctions.RHTower
