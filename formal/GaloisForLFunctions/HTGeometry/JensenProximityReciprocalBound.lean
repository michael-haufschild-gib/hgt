import Mathlib

/-!
# Jensen's inequality for the proximity of a reciprocal

For an entire `g` the divisor is non-negative, so its logarithmic counting function is non-negative
and Jensen's formula degrades to the mean value *inequality*

```text
log‖c(g)‖ ≤ ⨍ log‖g‖,
```

where `c(g)` is the trailing coefficient of `g` at the origin.  Splitting `log = log⁺ − log⁺ ∘ (·)⁻¹`
turns that into

```text
m(r, 1/g) ≤ m(r, g) − log‖c(g)‖.
```

Unlike the zero-free identity, this needs no hypothesis on the zeros of `g`: the zeros contribute a
non-negative counting term which only helps the inequality.  This is what discharges the ramification
term of the second main theorem for a function whose derivative is allowed to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Real ValueDistribution

/-- **The mean value inequality for `log‖g‖`.**  For an entire `g` and `1 ≤ r`, the circle average of
`log‖g‖` is at least the logarithm of the norm of the trailing coefficient at the origin.  Jensen's
formula expresses the difference as the logarithmic counting function of the divisor of `g`, which is
non-negative because an analytic function has a non-negative divisor. -/
theorem log_norm_trailingCoeff_le_circleAverage {g : ℂ → ℂ} (hg : Differentiable ℂ g) {r : ℝ}
    (hr : 1 ≤ r) :
    Real.log ‖meromorphicTrailingCoeffAt g 0‖ ≤ circleAverage (fun z => Real.log ‖g z‖) 0 r := by
  have hm : Meromorphic g := fun z => (hg.analyticAt z).meromorphicAt
  have hjen := Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
    (f := g) hm (R := r) (by linarith)
  have hA : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hnn : 0 ≤ MeromorphicOn.divisor g Set.univ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA
  have hpos := Function.locallyFinsuppWithin.logCounting_nonneg hnn hr
  linarith [hjen, hpos]

/-- **The proximity of a reciprocal, with zeros allowed.**  For an entire `g` and `1 ≤ r`,
`m(r, 1/g) ≤ m(r, g) − log‖c(g)‖`, where `c(g)` is the trailing coefficient of `g` at the origin.
The pointwise identity `log⁺x − log⁺x⁻¹ = log x` integrates to the mean value inequality. -/
theorem proximity_inv_le_sub {g : ℂ → ℂ} (hg : Differentiable ℂ g) {r : ℝ} (hr : 1 ≤ r) :
    proximity (fun z => (g z)⁻¹) ⊤ r
      ≤ proximity g ⊤ r - Real.log ‖meromorphicTrailingCoeffAt g 0‖ := by
  have hintg : CircleIntegrable (fun z => Real.posLog ‖g z‖) 0 r :=
    ((Real.continuous_posLog.comp (continuous_norm.comp hg.continuous)).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hminv : MeromorphicOn (fun z => (g z)⁻¹) (Metric.sphere (0 : ℂ) |r|) :=
    fun z _ => ((hg.analyticAt z).meromorphicAt).inv
  have hintinv : CircleIntegrable (fun z => Real.posLog ‖(g z)⁻¹‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm hminv
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
  have hmv := log_norm_trailingCoeff_le_circleAverage hg hr
  rw [ValueDistribution.proximity_top, ValueDistribution.proximity_top]
  linarith [hsub, hmv]

end GaloisForLFunctions.HTGeometry
