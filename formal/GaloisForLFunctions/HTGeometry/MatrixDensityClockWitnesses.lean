import GaloisForLFunctions.HTGeometry.WeightedBivariateMarginalLock

/-!
# Realizations of the density-clock cyclicity interface

A constant clock is central in the matrix algebra, so its diagonal commutes with every matrix and
the density pairing cannot see the order of multiplication.  Constant clocks therefore realize the
cyclicity interface for every density.
-/

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A constant clock is cyclic for every density. -/
theorem matrixDensityClockCyclic_const (density : Matrix I I ℝ) (c : ℝ) :
    MatrixDensityClockCyclic density (fun _ => c) := by
  intro A
  have hcomm : Matrix.diagonal (fun _ : I => c) * A =
      A * Matrix.diagonal (fun _ : I => c) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  rw [hcomm]

end GaloisForLFunctions.HTGeometry
