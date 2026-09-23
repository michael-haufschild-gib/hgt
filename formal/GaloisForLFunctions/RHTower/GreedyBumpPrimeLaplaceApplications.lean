import GaloisForLFunctions.RHTower.PrimeLaplaceGramStrict
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for strict prime-Laplace packets

Distinct positive Laplace nodes give a strictly positive von-Mangoldt Gram matrix.  Its doubled-real
form is therefore a template metric for arXiv:2609.03581.  A packet of `N` complex nodes exposes
`2N` real profiling directions and leading bias `N/Q`.
-/

open Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Certified finite packet of distinct positive prime-Laplace nodes. -/
structure GreedyBumpPrimeLaplaceData (N : ℕ) where
  node : Fin N → ℝ
  node_pos : ∀ i, 0 < node i
  node_injective : Function.Injective node

/-- Doubled-real von-Mangoldt Gram matrix. -/
def GreedyBumpPrimeLaplaceData.realifiedMatrix {N : ℕ}
    (data : GreedyBumpPrimeLaplaceData N) : Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
    (GaloisForLFunctions.HTGeometry.complexMatrixRealification
    (vonMangoldtPrimeLaplaceGram data.node)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm

/-- Prime-Laplace Gram as a positive template metric. -/
def GreedyBumpPrimeLaplaceData.metric {N : ℕ}
    (data : GreedyBumpPrimeLaplaceData N) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric (N + N) where
  matrix := data.realifiedMatrix
  posDef := (GaloisForLFunctions.HTGeometry.complexMatrixRealification_posDef
    (vonMangoldtPrimeLaplaceGram_posDef data.node data.node_pos data.node_injective)).submatrix
      finSumFinEquiv.symm.injective

/-- Complete optimizer, trials, bias, and localization laws for the prime packet. -/
theorem GreedyBumpPrimeLaplaceData.laws {N : ℕ}
    (data : GreedyBumpPrimeLaplaceData N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q data.metric :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q data.metric

/-- `N` complex prime-Laplace nodes produce leading amplitude bias `N/Q`. -/
theorem GreedyBumpPrimeLaplaceData.bias {N : ℕ}
    (data : GreedyBumpPrimeLaplaceData N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q data.metric)⁻¹ *
          data.metric.matrix) =
      (N : ℝ) / (Q : ℝ) := by
  rw [GaloisForLFunctions.HTGeometry.greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Metric localization radius is `2N/Q²`. -/
theorem GreedyBumpPrimeLaplaceData.localizationRadius {N : ℕ}
    (data : GreedyBumpPrimeLaplaceData N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    Matrix.trace
        (GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance Q data.metric *
          data.metric.matrix) =
      ((N + N : ℕ) : ℝ) / (Q : ℝ) ^ (2 : ℕ) :=
  GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end RHTower
