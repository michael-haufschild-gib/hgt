import GaloisForLFunctions.RHTower.ExponentialPolynomialIntervalMoments
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for exponential-polynomial mode packets

Distinct complex frequencies, with arbitrary finite multiplicities, give a strictly positive
interval Gram matrix.  Its doubled-real form is therefore a template metric for arXiv:2609.03581.
The total complex mode multiplicity controls the universal bias and localization coefficients;
frequencies and interval endpoints control only the metric shape.
-/

open Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Certified exponential-polynomial packet on a nondegenerate real interval. -/
structure GreedyBumpExponentialModeData (r : ℕ) where
  frequency : Fin r → ℂ
  frequency_injective : Function.Injective frequency
  multiplicity : Fin r → ℕ
  left : ℝ
  right : ℝ
  interval_nonempty : left < right

/-- Total number of complex exponential-polynomial modes, including multiplicities. -/
def GreedyBumpExponentialModeData.modeCount {r : ℕ}
    (data : GreedyBumpExponentialModeData r) : ℕ :=
  ∑ i, data.multiplicity i

/-- Doubled-real interval Gram matrix of the exponential-polynomial packet. -/
def GreedyBumpExponentialModeData.realifiedMatrix {r : ℕ}
    (data : GreedyBumpExponentialModeData r) :
    Matrix (Fin (data.modeCount + data.modeCount))
      (Fin (data.modeCount + data.modeCount)) ℝ :=
  (GaloisForLFunctions.HTGeometry.complexMatrixRealification
      (exponentialPolynomialIntervalGram data.frequency data.multiplicity
        data.left data.right)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Exponential-polynomial interval Gram as a positive template metric. -/
def GreedyBumpExponentialModeData.metric {r : ℕ}
    (data : GreedyBumpExponentialModeData r) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric
      (data.modeCount + data.modeCount) where
  matrix := data.realifiedMatrix
  posDef := (GaloisForLFunctions.HTGeometry.complexMatrixRealification_posDef
    (exponentialPolynomialIntervalGram_posDef data.frequency_injective
      data.multiplicity data.interval_nonempty)).submatrix finSumFinEquiv.symm.injective

/-- Complete optimizer, trials, bias, and localization laws for every certified mode packet. -/
theorem GreedyBumpExponentialModeData.laws {r : ℕ}
    (data : GreedyBumpExponentialModeData r)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q data.metric :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q data.metric

/-- A packet of `M` complex modes has leading amplitude bias `M / Q`. -/
theorem GreedyBumpExponentialModeData.bias {r : ℕ}
    (data : GreedyBumpExponentialModeData r)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q data.metric)⁻¹ *
          data.metric.matrix) =
      (data.modeCount : ℝ) / (Q : ℝ) := by
  rw [GaloisForLFunctions.HTGeometry.greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Metric-unit localization radius counts both real channels of every complex mode. -/
theorem GreedyBumpExponentialModeData.localizationRadius {r : ℕ}
    (data : GreedyBumpExponentialModeData r)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    Matrix.trace
        (GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance Q data.metric *
          data.metric.matrix) =
      ((data.modeCount + data.modeCount : ℕ) : ℝ) / (Q : ℝ) ^ (2 : ℕ) :=
  GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end RHTower
