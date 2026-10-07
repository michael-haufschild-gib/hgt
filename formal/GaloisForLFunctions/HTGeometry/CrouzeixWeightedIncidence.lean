import GaloisForLFunctions.HTGeometry.CrouzeixGramEnergy

/-!
# Positive-block energy for weighted incidence and replica kernels

The Crouzeix Gram-block deficit identifies exactly the covariance information retained by
weighted sheet--target incidence. At each replica order the same identity detects equality of
the corresponding tensor moments, without normalization, nonzero-weight, or rank premises.
-/

open Matrix
open scoped BigOperators ComplexConjugate Matrix NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {h x y : Type*} [Fintype h] [Fintype x] [Fintype y]
  [DecidableEq h] [DecidableEq x] [DecidableEq y]

/-- Weighted cross-incidence energy has an exact covariance-distance deficit. -/
theorem finiteWeightedIncidence_energy_identity
    (a : x → ℝ≥0) (u : x → h → ℂ) (b : y → ℝ≥0) (v : y → h → ℂ) :
    finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix a u) +
        finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix b v) -
        2 * finiteMatrixHilbertSchmidtSq (finiteWeightedIncidenceMatrix a u b v) =
      finiteMatrixHilbertSchmidtSq
        (finiteWeightedCovarianceMatrix a u - finiteWeightedCovarianceMatrix b v) := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality,
    finiteWeightedSynthesisMatrix_mul_conjTranspose, finiteWeightedIncidenceMatrix] using
    crouzeix_gram_energy_identity (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v)

/-- Weighted incidence cannot exceed the arithmetic mean of the covariance energies. -/
theorem finiteWeightedIncidence_energy_bound
    (a : x → ℝ≥0) (u : x → h → ℂ) (b : y → ℝ≥0) (v : y → h → ℂ) :
    2 * finiteMatrixHilbertSchmidtSq (finiteWeightedIncidenceMatrix a u b v) ≤
      finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix a u) +
        finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix b v) := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality,
    finiteWeightedSynthesisMatrix_mul_conjTranspose, finiteWeightedIncidenceMatrix] using
    crouzeix_gram_energy_bound (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v)

/-- Maximal weighted coupling is equivalent to equality of source and target covariances. -/
theorem finiteWeightedIncidence_energy_saturation
    (a : x → ℝ≥0) (u : x → h → ℂ) (b : y → ℝ≥0) (v : y → h → ℂ) :
    2 * finiteMatrixHilbertSchmidtSq (finiteWeightedIncidenceMatrix a u b v) =
        finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix a u) +
          finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix b v) ↔
      finiteWeightedCovarianceMatrix a u = finiteWeightedCovarianceMatrix b v := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality,
    finiteWeightedSynthesisMatrix_mul_conjTranspose, finiteWeightedIncidenceMatrix] using
    crouzeix_gram_energy_saturation (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v)

/-- A discrepancy in any covariance entry certifies a strict positive-block energy deficit. -/
theorem finiteWeightedIncidence_covariance_entry_bound
    (a : x → ℝ≥0) (u : x → h → ℂ) (b : y → ℝ≥0) (v : y → h → ℂ) (i j : h) :
    ‖finiteWeightedCovarianceMatrix a u i j - finiteWeightedCovarianceMatrix b v i j‖ ^ 2 ≤
      finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix a u) +
        finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix b v) -
        2 * finiteMatrixHilbertSchmidtSq (finiteWeightedIncidenceMatrix a u b v) := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality,
    finiteWeightedSynthesisMatrix_mul_conjTranspose, finiteWeightedIncidenceMatrix] using
    crouzeix_gram_energy_entry_bound (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v) i j

/-- Every replica order has the same exact covariance-distance law. -/
theorem finiteWeightedReplicaIncidence_energy_identity
    (r : ℕ) (a : x → ℝ≥0) (u : x → h → ℂ) (b : y → ℝ≥0) (v : y → h → ℂ) :
    finiteMatrixHilbertSchmidtSq
        (finiteWeightedCovarianceMatrix a (fun i => finitePureTensorPowerEuclidean r (u i))) +
      finiteMatrixHilbertSchmidtSq
        (finiteWeightedCovarianceMatrix b (fun j => finitePureTensorPowerEuclidean r (v j))) -
      2 * finiteMatrixHilbertSchmidtSq
        (finiteWeightedIncidenceMatrix a (fun i => finitePureTensorPowerEuclidean r (u i))
          b (fun j => finitePureTensorPowerEuclidean r (v j))) =
      finiteMatrixHilbertSchmidtSq
        (finiteWeightedCovarianceMatrix a (fun i => finitePureTensorPowerEuclidean r (u i)) -
          finiteWeightedCovarianceMatrix b (fun j => finitePureTensorPowerEuclidean r (v j))) :=
  finiteWeightedIncidence_energy_identity a _ b _

/-- Saturation at replica order `r` detects equality of the complete tensor covariances. -/
theorem finiteWeightedReplicaIncidence_energy_saturation
    (r : ℕ) (a : x → ℝ≥0) (u : x → h → ℂ) (b : y → ℝ≥0) (v : y → h → ℂ) :
    2 * finiteMatrixHilbertSchmidtSq
        (finiteWeightedIncidenceMatrix a (fun i => finitePureTensorPowerEuclidean r (u i))
          b (fun j => finitePureTensorPowerEuclidean r (v j))) =
        finiteMatrixHilbertSchmidtSq
          (finiteWeightedCovarianceMatrix a (fun i => finitePureTensorPowerEuclidean r (u i))) +
        finiteMatrixHilbertSchmidtSq
          (finiteWeightedCovarianceMatrix b (fun j => finitePureTensorPowerEuclidean r (v j))) ↔
      finiteWeightedCovarianceMatrix a (fun i => finitePureTensorPowerEuclidean r (u i)) =
        finiteWeightedCovarianceMatrix b (fun j => finitePureTensorPowerEuclidean r (v j)) :=
  finiteWeightedIncidence_energy_saturation a _ b _

end

end GaloisForLFunctions.HTGeometry
