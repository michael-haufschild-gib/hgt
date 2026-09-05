import GaloisForLFunctions.HTGeometry.NoncommutativeQubitExponentialFormation
import GaloisForLFunctions.HTGeometry.GreedyBumpKrausApplications

/-!
# Greedy-bump geometry on noncommutative qubit densities

Every finite-parameter qubit exponential density is positive definite.  Its doubled-real form is
therefore a four-direction template metric carrying all local-search identities of
arXiv:2609.03581.
-/

open Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Doubled-real qubit density as a positive four-direction template metric. -/
def greedyBumpQubitDensityMetric (b t : ℝ) : PositiveTemplateMetric (2 + 2) where
  matrix := greedyBumpKrausRealifiedMatrix (qubitDensity b t)
  posDef := (complexMatrixRealification_posDef (qubitDensity_posDef b t)).submatrix
    finSumFinEquiv.symm.injective

/-- Full optimizer, trials, localization, covariance, and bias package for a qubit density. -/
theorem greedyBumpQubitDensity_laws (b t : ℝ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpQubitDensityMetric b t) :=
  greedyBumpMetricLaws_closed Q (greedyBumpQubitDensityMetric b t)

/-- A two-level complex density contributes two signal-normalized units of matched bias after
faithful realification. -/
theorem greedyBumpQubitDensity_bias (b t : ℝ) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpQubitDensityMetric b t))⁻¹ *
          (greedyBumpQubitDensityMetric b t).matrix) =
      2 / (Q : ℝ) := by
  rw [greedyBump_matched_bias]
  field_simp [ne_of_gt Q.property]
  ring

/-- Reflection changes the noncommutative state but leaves matched search bias invariant. -/
theorem greedyBumpQubitDensity_bias_reflectionInvariant
    (b t : ℝ) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpQubitDensityMetric b t))⁻¹ *
          (greedyBumpQubitDensityMetric b t).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpQubitDensityMetric b (-t)))⁻¹ *
          (greedyBumpQubitDensityMetric b (-t)).matrix) := by
  rw [greedyBumpQubitDensity_bias, greedyBumpQubitDensity_bias]

end

end GaloisForLFunctions.HTGeometry
