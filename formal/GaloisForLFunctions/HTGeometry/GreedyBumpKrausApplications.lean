import GaloisForLFunctions.HTGeometry.FiniteBuresKrausDataProcessingLaw
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump geometry under Kraus pullback

A normalized rectangular Kraus channel pulls every positive-definite output reporter back to a
positive-definite input reporter.  After doubled-real transport, both reporters satisfy the
local-search identities of arXiv:2609.03581.  Their leading biases depend only on input/output
carrier dimensions.
-/

open Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive output reporter attached to a normalized rectangular Kraus channel. -/
structure GreedyBumpKrausReporter
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (channel : FiniteRectangularKrausChannel dIn dOut κ) where
  reporter : Matrix (Fin dOut) (Fin dOut) ℂ
  reporter_posDef : reporter.PosDef

/-- Canonically reindex a doubled-real complex matrix. -/
def greedyBumpKrausRealifiedMatrix {D : ℕ}
    (A : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin (D + D)) (Fin (D + D)) ℝ :=
  (complexMatrixRealification A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Output reporter as a real template metric. -/
def GreedyBumpKrausReporter.outputMetric
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {channel : FiniteRectangularKrausChannel dIn dOut κ}
    (data : GreedyBumpKrausReporter channel) : PositiveTemplateMetric (dOut + dOut) where
  matrix := greedyBumpKrausRealifiedMatrix data.reporter
  posDef := (complexMatrixRealification_posDef data.reporter_posDef).submatrix
    finSumFinEquiv.symm.injective

/-- Kraus-pulled reporter as a real input template metric. -/
def GreedyBumpKrausReporter.pullbackMetric
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {channel : FiniteRectangularKrausChannel dIn dOut κ}
    (data : GreedyBumpKrausReporter channel) : PositiveTemplateMetric (dIn + dIn) where
  matrix := greedyBumpKrausRealifiedMatrix (channel.pullbackMatrix data.reporter)
  posDef := (complexMatrixRealification_posDef
    (channel.pullbackMatrix_posDef data.reporter_posDef)).submatrix
      finSumFinEquiv.symm.injective

/-- Full local-search package for a positive output reporter. -/
theorem GreedyBumpKrausReporter.output_laws
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {channel : FiniteRectangularKrausChannel dIn dOut κ}
    (data : GreedyBumpKrausReporter channel) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q data.outputMetric :=
  greedyBumpMetricLaws_closed Q data.outputMetric

/-- Full local-search package survives normalized Kraus pullback. -/
theorem GreedyBumpKrausReporter.pullback_laws
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {channel : FiniteRectangularKrausChannel dIn dOut κ}
    (data : GreedyBumpKrausReporter channel) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q data.pullbackMetric :=
  greedyBumpMetricLaws_closed Q data.pullbackMetric

/-- Output reporter bias is output complex dimension divided by signal. -/
theorem GreedyBumpKrausReporter.output_bias
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {channel : FiniteRectangularKrausChannel dIn dOut κ}
    (data : GreedyBumpKrausReporter channel) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q data.outputMetric)⁻¹ * data.outputMetric.matrix) =
      (dOut : ℝ) / (Q : ℝ) := by
  rw [greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Pulled reporter bias is input complex dimension divided by signal. -/
theorem GreedyBumpKrausReporter.pullback_bias
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {channel : FiniteRectangularKrausChannel dIn dOut κ}
    (data : GreedyBumpKrausReporter channel) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q data.pullbackMetric)⁻¹ * data.pullbackMetric.matrix) =
      (dIn : ℝ) / (Q : ℝ) := by
  rw [greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Dimension-preserving channels change reporter geometry but leave matched bias invariant. -/
theorem GreedyBumpKrausReporter.bias_dimensionPreserving
    {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {channel : FiniteRectangularKrausChannel d d κ}
    (data : GreedyBumpKrausReporter channel) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q data.outputMetric)⁻¹ * data.outputMetric.matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q data.pullbackMetric)⁻¹ * data.pullbackMetric.matrix) := by
  rw [data.output_bias, data.pullback_bias]

end

end GaloisForLFunctions.HTGeometry
