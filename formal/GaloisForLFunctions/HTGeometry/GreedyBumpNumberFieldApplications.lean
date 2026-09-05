import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanPrimitiveMinimum
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump geometry on number-field archimedean forms

The canonical archimedean form of a number field is a positive real metric on
`n * [K : ℚ]` coordinates.  The local-search laws of arXiv:2609.03581 therefore apply without
reference to signature or the individual placewise forms.
-/

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Canonical archimedean number-field form as a positive template metric. -/
def greedyBumpNumberFieldArchimedeanMetric {n : ℕ}
    (A : numberFieldArchimedeanPositiveForms K n) :
    PositiveTemplateMetric (n * Module.finrank ℚ K) where
  matrix := numberFieldArchimedeanCanonicalMatrix A
  posDef := numberFieldArchimedeanCanonicalMatrix_posDef A

/-- Complete optimizer, trials, localization, covariance, and bias laws on every canonical
archimedean form. -/
theorem greedyBumpNumberFieldArchimedean_laws {n : ℕ}
    (A : numberFieldArchimedeanPositiveForms K n) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpNumberFieldArchimedeanMetric A) :=
  greedyBumpMetricLaws_closed Q (greedyBumpNumberFieldArchimedeanMetric A)

/-- Matched archimedean profiling bias counts exactly `n * [K : ℚ]` real directions. -/
theorem greedyBumpNumberFieldArchimedean_bias {n : ℕ}
    (A : numberFieldArchimedeanPositiveForms K n) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpNumberFieldArchimedeanMetric A))⁻¹ *
          (greedyBumpNumberFieldArchimedeanMetric A).matrix) =
      ((n * Module.finrank ℚ K : ℕ) : ℝ) / (2 * (Q : ℝ)) :=
  greedyBump_matched_bias Q (greedyBumpNumberFieldArchimedeanMetric A)

/-- At fixed rank and field degree, changing every local positive form leaves matched bias
unchanged. -/
theorem greedyBumpNumberFieldArchimedean_bias_formInvariant {n : ℕ}
    (A B : numberFieldArchimedeanPositiveForms K n) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpNumberFieldArchimedeanMetric A))⁻¹ *
          (greedyBumpNumberFieldArchimedeanMetric A).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpNumberFieldArchimedeanMetric B))⁻¹ *
          (greedyBumpNumberFieldArchimedeanMetric B).matrix) := by
  rw [greedyBump_matched_bias, greedyBump_matched_bias]

end

end GaloisForLFunctions.HTGeometry
