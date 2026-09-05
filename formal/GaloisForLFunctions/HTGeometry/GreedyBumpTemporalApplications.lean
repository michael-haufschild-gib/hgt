import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.HTGeometry.ObserverReturnTemporalCoercivityLaw

/-!
# Greedy-bump laws for observer temporal metrics

Positive observer weights and separation turn finite gap coordinates into a
strict template metric.  The complete local-search package then applies.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Admissible observer-visible temporal coordinate system. -/
structure GreedyBumpObserverTemporalData (J : Type*) [Fintype J] (D : ℕ) where
  weight : J → ℝ
  gap : J → Fin D → ℝ
  weightPos : ∀ j, 0 < weight j
  nondegenerate : ObserverTemporalMetricNondegenerate gap

/-- Observer gap Gram viewed as a greedy-bump template metric. -/
def GreedyBumpObserverTemporalData.metric
    {J : Type*} [Fintype J] {D : ℕ}
    (A : GreedyBumpObserverTemporalData J D) : PositiveTemplateMetric D where
  matrix := observerTemporalGramMatrix A.weight A.gap
  posDef := observerTemporalGramMatrix_posDef
    A.weight A.gap A.weightPos A.nondegenerate

/-- All fourteen profiling, bias, trials, and localization laws hold for observer clocks. -/
theorem greedyBump_observerTemporal_laws
    {J : Type*} [Fintype J] {D : ℕ}
    (A : GreedyBumpObserverTemporalData J D) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q A.metric :=
  greedyBumpMetricLaws_closed Q A.metric

/-- Equal-dimensional observer clocks have identical matched local bias. -/
theorem greedyBump_observerTemporal_bias_universal
    {J K : Type*} [Fintype J] [Fintype K] {D : ℕ}
    (A : GreedyBumpObserverTemporalData J D)
    (B : GreedyBumpObserverTemporalData K D) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q A.metric)⁻¹ * A.metric.matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q B.metric)⁻¹ * B.metric.matrix) := by
  rw [(greedyBump_observerTemporal_laws A Q).localBias,
    (greedyBump_observerTemporal_laws B Q).localBias]

end

end GaloisForLFunctions.HTGeometry
