import GaloisForLFunctions.RHTower.SteinhausSecondMoments

/-!
# The second-order behaviour of the circle cumulant at the origin

`log I₀(0) = 0`, `(log I₀)'(0) = E[proj] = 0`, `(log I₀)''(0) = Var(proj) = 1/2`, hence
`log I₀(x)/x² → 1/4`.  This is the card's `(17)` and the constant of the sub-critical regime.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace HTGeometry

local instance phaseCirclePositiveTaylor : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

theorem mem_interior_integrableExpSet (v : ℝ) :
    v ∈ interior (integrableExpSet steinhausProjection
      (AddCircle.haarAddCircle (T := 2 * Real.pi))) := by
  simp [integrableExpSet_steinhausProjection]

/-- **The cumulant has vanishing first derivative at the origin.** -/
theorem deriv_steinhausLogLaplace_zero : deriv steinhausLogLaplace 0 = 0 := by
  have hcgf : steinhausLogLaplace
      = cgf steinhausProjection (AddCircle.haarAddCircle (T := 2 * Real.pi)) := rfl
  rw [hcgf, ProbabilityTheory.deriv_cgf (mem_interior_integrableExpSet 0)]
  have hnum : (∫ ω : PhaseCircle, steinhausProjection ω * Real.exp (0 * steinhausProjection ω)
      ∂AddCircle.haarAddCircle) = 0 := by
    simpa using integral_steinhausProjection_eq_zero
  rw [hnum, zero_div]

/-- **The cumulant has second derivative `1/2` at the origin.** -/
theorem iteratedDeriv_two_steinhausLogLaplace_zero :
    iteratedDeriv 2 steinhausLogLaplace 0 = 1 / 2 := by
  have hcgf : steinhausLogLaplace
      = cgf steinhausProjection (AddCircle.haarAddCircle (T := 2 * Real.pi)) := rfl
  have hd := deriv_steinhausLogLaplace_zero
  rw [hcgf] at hd
  rw [hcgf, ProbabilityTheory.iteratedDeriv_two_cgf_eq_integral
    (mem_interior_integrableExpSet 0), hd]
  have hmgf : mgf steinhausProjection (AddCircle.haarAddCircle (T := 2 * Real.pi)) 0 = 1 := by
    have : steinhausLaplace 0 = 1 := steinhausLaplace_zero
    exact this
  rw [hmgf, div_one]
  have hint : (∫ ω : PhaseCircle, (steinhausProjection ω - 0) ^ (2 : ℕ)
      * Real.exp (0 * steinhausProjection ω) ∂AddCircle.haarAddCircle)
      = ∫ ω : PhaseCircle, steinhausProjection ω ^ (2 : ℕ) ∂AddCircle.haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    simp
  rw [hint, integral_steinhausProjection_sq]

theorem differentiable_steinhausLogLaplace : Differentiable ℝ steinhausLogLaplace :=
  differentiableOn_univ.mp analyticOnNhd_steinhausLogLaplace.differentiableOn

theorem analyticOnNhd_deriv_steinhausLogLaplace :
    AnalyticOnNhd ℝ (deriv steinhausLogLaplace) Set.univ :=
  analyticOnNhd_steinhausLogLaplace.deriv

/-- **The quadratic behaviour of the cumulant at the origin.**  This is the card's `(17)`. -/
theorem tendsto_steinhausLogLaplace_div_sq :
    Filter.Tendsto (fun x : ℝ => steinhausLogLaplace x / x ^ (2 : ℕ))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 / 4)) := by
  have hd2 : DifferentiableAt ℝ (deriv steinhausLogLaplace) 0 :=
    (analyticOnNhd_deriv_steinhausLogLaplace 0 (Set.mem_univ 0)).differentiableAt
  have hderiv2 : deriv (deriv steinhausLogLaplace) 0 = 1 / 2 := by
    have h := iteratedDeriv_two_steinhausLogLaplace_zero
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at h
  have hslope : Filter.Tendsto (slope (deriv steinhausLogLaplace) 0)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 / 2)) := by
    have hderiv : HasDerivAt (deriv steinhausLogLaplace) (1 / 2) 0 := by
      have := hd2.hasDerivAt
      rwa [hderiv2] at this
    exact hasDerivAt_iff_tendsto_slope.1 hderiv
  have hratio : Filter.Tendsto (fun x : ℝ => deriv steinhausLogLaplace x / (2 * x))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 / 4)) := by
    have hhalf : Filter.Tendsto (fun x : ℝ => slope (deriv steinhausLogLaplace) 0 x / 2)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 / 2 / 2)) := hslope.div_const 2
    have hval : (1 : ℝ) / 2 / 2 = 1 / 4 := by norm_num
    rw [hval] at hhalf
    refine hhalf.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    rw [slope_def_field, deriv_steinhausLogLaplace_zero]
    field_simp
    ring
  refine HasDerivAt.lhopital_zero_nhdsNE ?_ ?_ ?_ ?_ ?_ hratio
  · filter_upwards with x
    exact (differentiable_steinhausLogLaplace x).hasDerivAt
  · filter_upwards with x
    have hp : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ)) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact hp
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    simpa using hx0
  · have hcont : Filter.Tendsto steinhausLogLaplace (nhds 0) (nhds 0) := by
      have h := continuous_steinhausLogLaplace.tendsto 0
      simpa using h
    exact hcont.mono_left nhdsWithin_le_nhds
  · have hcont : Filter.Tendsto (fun x : ℝ => x ^ (2 : ℕ)) (nhds 0) (nhds 0) := by
      have h := (continuous_pow 2).tendsto (0 : ℝ)
      simpa using h
    exact hcont.mono_left nhdsWithin_le_nhds

end

end HTGeometry
