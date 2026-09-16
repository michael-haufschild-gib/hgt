import GaloisForLFunctions.RHTower.PrimeLogThetaStripReporterBoundary

/-!
# Literal lower-half theta landing on the closed critical Laplace graph

For each `0 < t < 1`, the literal finite-prime theta transform at `w = -i t` is represented by
the canonical lower-half source reporter already identified from the critical Laplace feature.
This file composes that reporter with the source projection of the actual closed graph
`Graph(cl primeLogCriticalLaplaceSynthesis)` and proves exact agreement on every retained finite
graph-core point:

```text
Theta(core(x))(-i t) = XiC(-i t) * lowerGraphEvaluation_t(corePoint(x)).
```

The construction uses the literal finite theta transform and the canonical closure, with no
cutoff, source reweighting, Xi division, or replacement completion.  It is deliberately only a
lower-half-strip landing.  The real-axis reporter is formally unavailable in source `ℓ²`, and the
remaining PHCCED gate is still the Xi-adic, cubic-clock relative boundary morphism—not a family
of scalar evaluations.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

private theorem lowerReporter_inner_srcEmb
    (t : ℝ) (ht : 0 < t) (l : Nat.Primes →₀ ℂ) :
    inner ℂ (primeLogThetaStripLowerReporter t ht)
      (HTGeometry.ConstraintMotiveRelativity.srcEmb l) =
      (t : ℂ)⁻¹ * ∑ p ∈ l.support,
        l p * primeLogCriticalLaplaceFeatureC p t := by
  rw [primeLogThetaStripLowerReporter, inner_smul_left]
  have hstar : (starRingEnd ℂ) (t : ℂ)⁻¹ = (t : ℂ)⁻¹ := by
    simp
  rw [hstar, ← primeLogCriticalLaplaceMass_pointwise_eq_inner]

/-- Exact literal theta evaluation on the lower imaginary ray as a source inner product. -/
theorem primeLogThetaFourierLaplace_lowerReporter
    (t : ℝ) (ht : 0 < t) (htstrip : t < 1) (l : Nat.Primes →₀ ℂ) :
    primeLogThetaFourierLaplace l (-I * (t : ℂ)) =
      XiC (-I * (t : ℂ)) *
        inner ℂ (primeLogThetaStripLowerReporter t ht)
          (HTGeometry.ConstraintMotiveRelativity.srcEmb l) := by
  have htheta := mul_primeLogThetaFourierLaplace_neg_I_eq_XiC_mul_graph l ht htstrip
  have hinner := lowerReporter_inner_srcEmb t ht l
  rw [hinner]
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  calc
    primeLogThetaFourierLaplace l (-I * (t : ℂ)) =
        (t : ℂ)⁻¹ * ((t : ℂ) * primeLogThetaFourierLaplace l (-I * (t : ℂ))) := by
      field_simp
    _ = (t : ℂ)⁻¹ *
        (XiC (-I * (t : ℂ)) *
          ∑ p ∈ l.support, l p * primeLogCriticalLaplaceFeatureC p t) := by rw [htheta]
    _ = XiC (-I * (t : ℂ)) *
        ((t : ℂ)⁻¹ * ∑ p ∈ l.support,
          l p * primeLogCriticalLaplaceFeatureC p t) := by ring

/-- The canonical lower-half theta evaluation is a linear functional on the actual closed
critical-Laplace graph, through its source coordinate. -/
def primeLogThetaLowerClosedGraphEvaluation (t : ℝ) (ht : 0 < t) :
    primeLogCriticalLaplaceSynthesis.closure.graph →ₗ[ℂ] ℂ where
  toFun z := inner ℂ (primeLogThetaStripLowerReporter t ht) z.1.1
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Each literal finite graph-core point belongs to the canonical closed graph. -/
def primeLogCriticalLaplaceClosureCorePoint
    (x : primeLogCriticalLaplaceSynthesis.domain) :
    primeLogCriticalLaplaceSynthesis.closure.graph :=
  ⟨((x : primeLogCriticalSourceL2), primeLogCriticalLaplaceSynthesis x), by
    rw [← primeLogCriticalLaplaceSynthesis_isClosable.graph_closure_eq_closure_graph]
    exact primeLogCriticalLaplaceSynthesis.graph.le_topologicalClosure
      ((LinearPMap.mem_graph_iff primeLogCriticalLaplaceSynthesis).mpr ⟨x, rfl, rfl⟩)⟩

/-- Closed-graph lower evaluation restricts to the canonical inner-product reporter on the finite
source core. -/
theorem primeLogThetaLowerClosedGraphEvaluation_core
    (t : ℝ) (ht : 0 < t) (x : primeLogCriticalLaplaceSynthesis.domain) :
    primeLogThetaLowerClosedGraphEvaluation t ht
      (primeLogCriticalLaplaceClosureCorePoint x) =
      inner ℂ (primeLogThetaStripLowerReporter t ht) (x : primeLogCriticalSourceL2) := by
  rfl

/-- **Literal closed-graph lower landing.**  On every retained finite graph-core vector, the
bounded closed-graph functional is exactly the literal theta Fourier--Laplace transform. -/
theorem primeLogThetaFourierLaplace_closedGraphCore
    (t : ℝ) (ht : 0 < t) (htstrip : t < 1)
    (x : primeLogCriticalLaplaceSynthesis.domain) :
    primeLogThetaFourierLaplace (primeLogCriticalLaplaceCore x) (-I * (t : ℂ)) =
      XiC (-I * (t : ℂ)) *
        primeLogThetaLowerClosedGraphEvaluation t ht
          (primeLogCriticalLaplaceClosureCorePoint x) := by
  rw [primeLogThetaFourierLaplace_lowerReporter t ht htstrip]
  rw [srcEmb_primeLogCriticalLaplaceCore]
  rfl

end

end RHTower
