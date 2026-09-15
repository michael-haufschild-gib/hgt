import GaloisForLFunctions.RHTower.OscillatoryLogIntegral

/-!
# Exact logarithmic tail mass for the oscillatory prime phase

The off-pole prime-phase argument has a single nonuniform factor: integration by parts produces
`|lambda|⁻¹` times the positive logarithmic tail weight.  This file computes that tail exactly.
It gives the quantitative scale `1 / (|lambda| log U)` at a lower cutoff `U`, so any remaining
moving-phase obstruction must live in the boundary layer where this quantity does not vanish.

No prime estimate is used here; this is the analytic infrastructure shared by the PNT phase proof
and any source-faithful moving-frequency refinement.
-/

namespace RHTower

open Filter MeasureTheory Set
open scoped Topology

/-- Exact mass of the positive remainder tail produced by logarithmic phase integration by parts. -/
theorem integral_Ioi_logTailWeight_eq (U : ℝ) (hU : 1 < U) :
    ∫ t in Ioi U, (t * (Real.log t) ^ 2)⁻¹ = (Real.log U)⁻¹ := by
  have hcont : ContinuousWithinAt (fun x : ℝ => -(Real.log x)⁻¹) (Ici U) U := by
    have hlog : Real.log U ≠ 0 := (Real.log_pos hU).ne'
    exact ((Real.continuousAt_log (by linarith)).inv₀ hlog).neg.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi U,
      HasDerivAt (fun x : ℝ => -(Real.log x)⁻¹)
        ((x * (Real.log x) ^ 2)⁻¹) x := by
    intro x hx
    have hxU : U < x := hx
    exact hasDerivAt_negInvLog (lt_trans hU hxU)
  have hpos : ∀ x ∈ Ioi U, 0 ≤ (x * (Real.log x) ^ 2)⁻¹ := by
    intro x hx
    have hxU : U < x := hx
    have hx1 : 1 < x := lt_trans hU hxU
    positivity
  have hlim : Tendsto (fun x : ℝ => -(Real.log x)⁻¹) atTop (nhds 0) := by
    have hlogTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    simpa using hlogTop.inv_tendsto_atTop.neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  ring

/-- The positive logarithmic tail weight is integrable from every cutoff above one. -/
theorem integrableOn_logTailWeight_Ioi (U : ℝ) (hU : 1 < U) :
    IntegrableOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) (Ioi U) := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun x : ℝ => -(Real.log x)⁻¹) (l := 0)
    ?_ ?_ ?_ ?_
  · have hlog : Real.log U ≠ 0 := (Real.log_pos hU).ne'
    exact ((Real.continuousAt_log (by linarith)).inv₀ hlog).neg.continuousWithinAt
  · intro x hx
    exact hasDerivAt_negInvLog (lt_trans hU hx)
  · intro x hx
    have hx1 : 1 < x := lt_trans hU hx
    positivity
  · have hlogTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    simpa using hlogTop.inv_tendsto_atTop.neg

/-- Uniform outer-tail control for the integrated-by-parts phase remainder.

The exact scale is `(|lambda| * log U)⁻¹`.  Thus phase integration by parts controls every
moving regime with `|lambda| * log U → ∞`, and isolates the nonuniform boundary layer. -/
theorem norm_integral_Ioi_oscLogRemainder_le {lam U : ℝ} (hU : 1 < U) :
    ‖∫ t in Ioi U, oscLogRemainder lam t‖ ≤ |lam|⁻¹ * (Real.log U)⁻¹ := by
  have hmajor := (integrableOn_logTailWeight_Ioi U hU).const_mul |lam|⁻¹
  have hbound := norm_integral_le_of_norm_le hmajor (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_oscLogRemainder lam (lt_trans hU ht)])
  rw [integral_const_mul] at hbound
  calc
    ‖∫ t in Ioi U, oscLogRemainder lam t‖ ≤
        |lam|⁻¹ * ∫ t in Ioi U, (t * (Real.log t) ^ 2)⁻¹ := hbound
    _ = |lam|⁻¹ * (Real.log U)⁻¹ := by
      rw [integral_Ioi_logTailWeight_eq U hU]

end RHTower
