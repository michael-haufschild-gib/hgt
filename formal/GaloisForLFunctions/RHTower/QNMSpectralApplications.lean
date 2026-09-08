import GaloisForLFunctions.HilbertMetric.QNMMatrixBackwardError
import GaloisForLFunctions.RHTower.KrejcirikPseudospectrumApplications

/-!
# QNMSpectralApplications

The optical QNM backward-error characterization applies to Suzuki terminal
adjacency, coefficient-faithful Deninger Gamma-six blocks, and the nonnormal
Hermite Gaussian similarity. The minimum is over actual matrix perturbations.
-/

noncomputable section
open GaloisForLFunctions.HilbertMetric
open scoped Matrix.Norms.L2Operator
namespace RHTower

theorem onePrimeTerminalAdjacency_qnmBackwardError (z : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    IsLeast {r : ℝ | ∃ D : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (onePrimeTerminalAdjacency + D) v =
        z • v ∧ ‖D‖ = r}
      (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) onePrimeTerminalAdjacency v - z • v‖ / ‖v‖) := by
  simpa using qnmMatrixBackwardError_isLeast onePrimeTerminalAdjacency 1 z v

theorem deningerGammaSix_qnmBackwardError (delta : ℝ) (m : ℕ)
    (z : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    IsLeast {r : ℝ | ∃ D : Matrix (Fin 2) (Fin 2) ℝ,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)
        (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m + D) v = z • v ∧ ‖D‖ = r}
      (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)
        (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) v - z • v‖ / ‖v‖) := by
  simpa using qnmMatrixBackwardError_isLeast
    (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) 1 z v

theorem hermiteGaussian_qnmBackwardError (z : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    IsLeast {r : ℝ | ∃ D : Matrix (Fin 2) (Fin 2) ℝ,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)
        (hermiteEvenStepFourGaussianSimilarity 2 1 + D) v = z • v ∧ ‖D‖ = r}
      (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)
        (hermiteEvenStepFourGaussianSimilarity 2 1) v - z • v‖ / ‖v‖) := by
  simpa using qnmMatrixBackwardError_isLeast (hermiteEvenStepFourGaussianSimilarity 2 1) 1 z v

end RHTower
