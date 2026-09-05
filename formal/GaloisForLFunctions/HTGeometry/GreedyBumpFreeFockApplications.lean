import GaloisForLFunctions.HTGeometry.FreeFockMatrixFullAnalyticLaw
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump geometry on free-Fock matrix profiles

Positive free-Fock Stieltjes profiles are Hermitian metrics.  Realification and finite-index
transport turn them into real template metrics, so all local-search identities of arXiv:2609.03581
apply to imaginary-axis and Poisson profiles.
-/

open Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Certified finite free-Fock covariance data. -/
structure GreedyBumpFreeFockData (K : Type*) [Fintype K] [DecidableEq K] (D : ℕ) where
  matrix : K → Matrix (Fin D) (Fin D) ℂ
  hermitian : ∀ k, (matrix k)ᴴ = matrix k
  trivialCommonKernel : HasTrivialCommonKernel matrix

/-- Reindex a doubled-real Hermitian profile by the canonical `Fin (D + D)` coordinates. -/
def greedyBumpRealifiedFiniteMetricMatrix {D : ℕ}
    (A : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin (D + D)) (Fin (D + D)) ℝ :=
  (complexMatrixRealification A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Positive imaginary-axis Dyson profile as a real template metric. -/
def GreedyBumpFreeFockData.imaginaryAxisMetric
    {K : Type*} [Fintype K] [DecidableEq K] {D : ℕ}
    (data : GreedyBumpFreeFockData K D) (height : PositiveSignal) :
    PositiveTemplateMetric (D + D) where
  matrix := greedyBumpRealifiedFiniteMetricMatrix
    (freeFockMatrixImaginaryAxisProfile data.matrix data.hermitian
      data.trivialCommonKernel (height : ℝ))
  posDef := (complexMatrixRealification_posDef
    (freeFockMatrixImaginaryAxisProfile_posDef data.matrix data.hermitian
      data.trivialCommonKernel (height : ℝ) height.property)).submatrix
        finSumFinEquiv.symm.injective

/-- Positive Poisson profile at arbitrary real energy as a real template metric. -/
def GreedyBumpFreeFockData.poissonMetric
    {K : Type*} [Fintype K] [DecidableEq K] {D : ℕ}
    (data : GreedyBumpFreeFockData K D) (energy : ℝ) (height : PositiveSignal) :
    PositiveTemplateMetric (D + D) where
  matrix := greedyBumpRealifiedFiniteMetricMatrix
    (freeFockMatrixPoissonProfile data.matrix data.hermitian
      data.trivialCommonKernel energy (height : ℝ))
  posDef := (complexMatrixRealification_posDef
    (freeFockMatrixPoissonProfile_posDef data.matrix data.hermitian
      data.trivialCommonKernel energy (height : ℝ) height.property)).submatrix
        finSumFinEquiv.symm.injective

/-- Full optimizer, trials, localization, covariance, and bias laws on the imaginary-axis profile. -/
theorem GreedyBumpFreeFockData.imaginaryAxis_laws
    {K : Type*} [Fintype K] [DecidableEq K] {D : ℕ}
    (data : GreedyBumpFreeFockData K D) (height Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (data.imaginaryAxisMetric height) :=
  greedyBumpMetricLaws_closed Q (data.imaginaryAxisMetric height)

/-- Full optimizer, trials, localization, covariance, and bias laws on every Poisson profile. -/
theorem GreedyBumpFreeFockData.poisson_laws
    {K : Type*} [Fintype K] [DecidableEq K] {D : ℕ}
    (data : GreedyBumpFreeFockData K D) (energy : ℝ) (height Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (data.poissonMetric energy height) :=
  greedyBumpMetricLaws_closed Q (data.poissonMetric energy height)

/-- Energy translation changes the free-Fock profile but not matched bias at fixed realified
dimension. -/
theorem GreedyBumpFreeFockData.bias_energyInvariant
    {K : Type*} [Fintype K] [DecidableEq K] {D : ℕ}
    (data : GreedyBumpFreeFockData K D) (energy : ℝ) (height Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (data.imaginaryAxisMetric height))⁻¹ *
          (data.imaginaryAxisMetric height).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (data.poissonMetric energy height))⁻¹ *
          (data.poissonMetric energy height).matrix) := by
  rw [greedyBump_matched_bias, greedyBump_matched_bias]

end

end GaloisForLFunctions.HTGeometry
