import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite self-commutator Fano defect

This module isolates the finite matrix identity behind the one-dimensional coherent Fano
curvature law.  For a real square matrix `A`, the gap between the squared column energy and the
energy of `A ^ 2` is exactly half the Hilbert--Schmidt energy of the self-commutator
`A * Aᵀ - Aᵀ * A`.

The identity is unconditional finite-dimensional parent algebra.  Its later Hilbert-metric
application identifies Gaussian determinant curvature with compressed-annihilator
non-normality.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {n : Type*} [Fintype n]

/-- The squared Hilbert--Schmidt (Frobenius) energy of a finite real matrix. -/
def matrixHilbertSchmidtEnergy (A : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The finite self-commutator measuring failure of real normality. -/
def matrixSelfCommutator (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A * A.transpose - A.transpose * A

theorem matrixHilbertSchmidtEnergy_nonneg (A : Matrix n n ℝ) :
    0 ≤ matrixHilbertSchmidtEnergy A := by
  unfold matrixHilbertSchmidtEnergy
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _

theorem matrixHilbertSchmidtEnergy_eq_zero_iff (A : Matrix n n ℝ) :
    matrixHilbertSchmidtEnergy A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hi : (∑ j, A i j ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg (A i j)).mp h i (Finset.mem_univ i)
    have hij : A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (A i j)).mp
        hi j (Finset.mem_univ j)
    simpa using (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simp [matrixHilbertSchmidtEnergy]

/-- Coordinate Hilbert--Schmidt energy equals the usual transpose-product trace. -/
theorem matrixHilbertSchmidtEnergy_eq_trace_transpose_mul (A : Matrix n n ℝ) :
    matrixHilbertSchmidtEnergy A = Matrix.trace (A.transpose * A) := by
  simp only [matrixHilbertSchmidtEnergy, Matrix.trace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change A j i ^ 2 = A j i * A j i
  ring

/-- Row and column energies have equal squared traces for one matrix. -/
theorem trace_rowEnergy_sq_eq_trace_columnEnergy_sq (A : Matrix n n ℝ) :
    Matrix.trace ((A * A.transpose) * (A * A.transpose)) =
      Matrix.trace ((A.transpose * A) * (A.transpose * A)) := by
  calc
    Matrix.trace ((A * A.transpose) * (A * A.transpose)) =
        Matrix.trace (A * (A.transpose * A * A.transpose)) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace ((A.transpose * A * A.transpose) * A) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((A.transpose * A) * (A.transpose * A)) := by
      congr 1
      noncomm_ring

/-- The row--column cross trace is the energy of the matrix square. -/
theorem trace_rowEnergy_mul_columnEnergy_eq_squareEnergy (A : Matrix n n ℝ) :
    Matrix.trace ((A * A.transpose) * (A.transpose * A)) =
      matrixHilbertSchmidtEnergy (A * A) := by
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  calc
    Matrix.trace ((A * A.transpose) * (A.transpose * A)) =
        Matrix.trace (A * (A.transpose * A.transpose * A)) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace ((A.transpose * A.transpose * A) * A) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((A * A).transpose * (A * A)) := by
      congr 1
      rw [Matrix.transpose_mul]
      noncomm_ring

/-- The reverse row--column cross trace has the same square energy. -/
theorem trace_columnEnergy_mul_rowEnergy_eq_squareEnergy (A : Matrix n n ℝ) :
    Matrix.trace ((A.transpose * A) * (A * A.transpose)) =
      matrixHilbertSchmidtEnergy (A * A) := by
  rw [Matrix.trace_mul_comm]
  exact trace_rowEnergy_mul_columnEnergy_eq_squareEnergy A

/-- **Self-commutator defect identity.**  The one-matrix column-energy defect is exactly one
half of the self-commutator Hilbert--Schmidt energy. -/
theorem selfCommutator_energy_eq_two_mul_defect (A : Matrix n n ℝ) :
    matrixHilbertSchmidtEnergy (matrixSelfCommutator A) =
      2 * (Matrix.trace ((A.transpose * A) * (A.transpose * A)) -
        matrixHilbertSchmidtEnergy (A * A)) := by
  unfold matrixSelfCommutator
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.trace_sub]
  rw [trace_rowEnergy_sq_eq_trace_columnEnergy_sq A,
    trace_rowEnergy_mul_columnEnergy_eq_squareEnergy A,
    trace_columnEnergy_mul_rowEnergy_eq_squareEnergy A]
  ring

/-- The energy of `A ^ 2` never exceeds the squared column energy.  Equality holds precisely
when the self-commutator has zero Hilbert--Schmidt energy. -/
theorem squareEnergy_le_trace_columnEnergy_sq (A : Matrix n n ℝ) :
    matrixHilbertSchmidtEnergy (A * A) ≤
      Matrix.trace ((A.transpose * A) * (A.transpose * A)) := by
  have hnonneg := matrixHilbertSchmidtEnergy_nonneg (matrixSelfCommutator A)
  rw [selfCommutator_energy_eq_two_mul_defect] at hnonneg
  linarith

/-- Vanishing of the one-matrix Fano defect is equivalent to normality. -/
theorem trace_columnEnergy_sq_eq_squareEnergy_iff (A : Matrix n n ℝ) :
    Matrix.trace ((A.transpose * A) * (A.transpose * A)) =
        matrixHilbertSchmidtEnergy (A * A) ↔
      matrixSelfCommutator A = 0 := by
  rw [← matrixHilbertSchmidtEnergy_eq_zero_iff (matrixSelfCommutator A)]
  rw [selfCommutator_energy_eq_two_mul_defect]
  constructor <;> intro h
  · rw [h, sub_self, mul_zero]
  · nlinarith

/-- A nonzero self-commutator forces a strict Fano defect. -/
theorem squareEnergy_lt_trace_columnEnergy_sq_of_selfCommutator_ne_zero
    (A : Matrix n n ℝ) (hA : matrixSelfCommutator A ≠ 0) :
    matrixHilbertSchmidtEnergy (A * A) <
      Matrix.trace ((A.transpose * A) * (A.transpose * A)) := by
  refine lt_of_le_of_ne (squareEnergy_le_trace_columnEnergy_sq A) ?_
  intro h
  exact hA ((trace_columnEnergy_sq_eq_squareEnergy_iff A).mp h.symm)

end

end GaloisForLFunctions.HilbertMetric
