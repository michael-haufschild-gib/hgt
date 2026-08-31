import Mathlib

/-!
# Jensen's formula for a zero-free entire function, in proximity form

Mathlib's `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` gives the mean value property
`⨍ log‖g‖ = log‖g(0)‖` for a zero-free analytic `g`.  Splitting `log = log⁺ − log⁺ ∘ (·)⁻¹` turns that into

```text
m(r, 1/g) = m(r, g) − log‖g(0)‖,
```

which is how the ramification term of the second main theorem is discharged when the derivative of
the function under study happens to be zero-free — as it is for a solution of `F' = c(F)` that omits
every root of `c`.
-/

namespace GaloisForLFunctions.HTGeometry

open Real ValueDistribution

/-- **The proximity of a reciprocal.**  For a zero-free entire `g`,
`m(r, 1/g) = m(r, g) − log‖g(0)‖`.  This is Jensen's formula in proximity form: the pointwise
identity `log⁺x − log⁺x⁻¹ = log x` integrates to the mean value property. -/
theorem proximity_inv_eq_sub {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hne : ∀ z, g z ≠ 0)
    {r : ℝ} (_hr : r ≠ 0) :
    proximity (fun z => (g z)⁻¹) ⊤ r = proximity g ⊤ r - Real.log ‖g 0‖ := by
  have hintg : CircleIntegrable (fun z => Real.posLog ‖g z‖) 0 r :=
    ((Real.continuous_posLog.comp (continuous_norm.comp hg.continuous)).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hcontinv : Continuous fun z => (g z)⁻¹ := hg.continuous.inv₀ hne
  have hintinv : CircleIntegrable (fun z => Real.posLog ‖(g z)⁻¹‖) 0 r :=
    ((Real.continuous_posLog.comp (continuous_norm.comp hcontinv)).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hpt : ∀ z : ℂ, Real.posLog ‖g z‖ - Real.posLog ‖(g z)⁻¹‖ = Real.log ‖g z‖ := by
    intro z
    rw [norm_inv]
    exact Real.posLog_sub_posLog_inv
  have hsub : circleAverage (fun z => Real.posLog ‖g z‖) 0 r
      - circleAverage (fun z => Real.posLog ‖(g z)⁻¹‖) 0 r
      = circleAverage (fun z => Real.log ‖g z‖) 0 r := by
    rw [← circleAverage_sub hintg hintinv]
    congr 1
    funext z
    exact hpt z
  rw [ValueDistribution.proximity_top, ValueDistribution.proximity_top]
  have hmv : circleAverage (fun z => Real.log ‖g z‖) 0 r = Real.log ‖g 0‖ :=
    AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
      (fun z _ => hg.analyticAt z) (fun u _ => hne u)
  rw [hmv] at hsub
  linarith [hsub]

end GaloisForLFunctions.HTGeometry
