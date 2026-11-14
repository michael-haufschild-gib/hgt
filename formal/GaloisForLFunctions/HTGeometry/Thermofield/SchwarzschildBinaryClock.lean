import GaloisForLFunctions.HTGeometry.LeviCivita.SchwarzschildCauchySlices
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalGibbs
import GaloisForLFunctions.HTGeometry.Thermofield.EntropyApplications
import GaloisForLFunctions.HilbertMetric.QuantumInformation.FermionSpectralEntropy

/-!
# A common hyperbolic coordinate for clocks and binary Gibbs populations

Cogo's clock in arXiv:2611.15912 uses `artanh`, while the corpus's spin bath
has population imbalance `tanh b`. Their composition recovers exactly the
bias `b`. The fermion correlation entropy of arXiv:2611.13085, applied to the
same two-by-two bath matrix, is twice its density-matrix entropy: a binary
correlation spectrum counts both particle and hole occupations.
-/

noncomputable section
open scoped BigOperators Matrix
namespace GaloisForLFunctions.HTGeometry
open Real SchafferExl GaloisForLFunctions.HilbertMetric

/-- The bath imbalance parameter is exactly the normalized Schwarzschild clock coordinate. -/
theorem schwarzschildCauchyClock_spinBath (m b X : ℝ) :
    schwarzschildCauchyClock m
      (sqrt (1 + X ^ 2) * (2 * spinBathUpper (exp (-b)) - 1)) X =
        4 * exp m * b := by
  rw [spinBathUpper_gibbs]
  have he : 2 * ((1 + tanh b) / 2) - 1 = tanh b := by ring
  rw [he]
  exact schwarzschildCauchyClock_slice m b X

/-- The actual bath matrix is a real diagonal occupation spectrum. -/
theorem spinBathDensity_real_diagonal (u : ℝ) :
    spinBathDensity u = Matrix.diagonal
      (fun i => ((![(spinBathUpper u), (1 - spinBathUpper u)] : Fin 2 → ℝ) i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinBathDensity, spinBathLower]

/-- Treating the two bath eigenvalues as fermion occupations counts particle and hole entropy. -/
theorem spinBathDensity_fermion_entropy (u : ℝ) :
    fermionSpectralEntropy (spinBathDensity u) = 2 * Real.binEntropy (spinBathUpper u) := by
  rw [spinBathDensity_real_diagonal, fermionSpectralEntropy_diagonal]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.binEntropy_one_sub]
  ring

/-- As a density matrix the same bath has only one binary entropy. -/
theorem spinBathDensity_vonNeumann_entropy (u : ℝ) :
    finiteMatrixVonNeumannEntropy (spinBathDensity u)
      (spinBathDensity_posSemidef u).isHermitian = Real.binEntropy (spinBathUpper u) := by
  rw [spinBathDensity_real_diagonal]
  rw [Thermofield.vonNeumannEntropy_real_diagonal]
  simp only [entropy, tsum_fintype, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.binEntropy, Real.log_inv]
  ring

/-- Mechanical entropy transfer between correlation and density interpretations has factor two. -/
theorem spinBathDensity_entropy_factor_two (u : ℝ) :
    fermionSpectralEntropy (spinBathDensity u) =
      2 * finiteMatrixVonNeumannEntropy (spinBathDensity u)
        (spinBathDensity_posSemidef u).isHermitian := by
  rw [spinBathDensity_fermion_entropy, spinBathDensity_vonNeumann_entropy]

end GaloisForLFunctions.HTGeometry

-- BEGIN PAPER AXIOM AUDIT
#print axioms GaloisForLFunctions.HTGeometry.schwarzschildCauchyClock_spinBath
#print axioms GaloisForLFunctions.HTGeometry.spinBathDensity_real_diagonal
#print axioms GaloisForLFunctions.HTGeometry.spinBathDensity_fermion_entropy
#print axioms GaloisForLFunctions.HTGeometry.spinBathDensity_vonNeumann_entropy
#print axioms GaloisForLFunctions.HTGeometry.spinBathDensity_entropy_factor_two
-- END PAPER AXIOM AUDIT
