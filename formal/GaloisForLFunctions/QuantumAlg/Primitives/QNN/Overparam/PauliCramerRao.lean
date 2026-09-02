import GaloisForLFunctions.QuantumAlg.Util.QuantumCramerRao
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Overparam.QuantumFisherRank
import Mathlib.Algebra.Order.Star.Real

/-!
# Cramer--Rao geometry of the Pauli-X QFIM witness

The corpus's concrete one-qubit rank witness has QFIM `[4]`.  This module
promotes it to a positive QFIM and evaluates the trace-inverse error and
determinant sloppiness from arXiv:2608.25870 exactly.
-/

namespace QuantumAlg

open Matrix

noncomputable section

/-- Exact matrix form of the existing one-qubit Pauli-X QFIM witness. -/
theorem qfim_ket0_pauliX2_eq_diagonal_four :
    qfim ket0 (fun _ : Fin 1 => pauliX2) =
      Matrix.diagonal (fun _ : Fin 1 => (4 : ℝ)) := by
  have h40 : (qfim ket0 (fun _ : Fin 1 => pauliX2)) 0 0 = 4 := by
    simp [qfim_apply, qCov, expval, ket0, pauliX2, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_two]
  ext i j
  fin_cases i
  fin_cases j
  simpa [Matrix.diagonal] using h40

/-- The Pauli-X witness as an identifiable one-parameter Fisher model. -/
def pauliXPositiveQFIM : PositiveQFIM 0 where
  matrix := qfim ket0 (fun _ : Fin 1 => pauliX2)
  posDef := by
    rw [qfim_ket0_pauliX2_eq_diagonal_four, Matrix.posDef_diagonal_iff]
    intro i
    norm_num

/-- Exact one-shot total SLD error of the Pauli-X witness. -/
theorem pauliXPositiveQFIM_sldCramerRao :
    pauliXPositiveQFIM.sldCramerRao = 1 / 4 := by
  simp [PositiveQFIM.sldCramerRao, pauliXPositiveQFIM,
    qfim_ket0_pauliX2_eq_diagonal_four]

/-- Exact determinant sloppiness of the one-dimensional Pauli-X model. -/
theorem pauliXPositiveQFIM_sloppiness :
    pauliXPositiveQFIM.sloppiness = 1 / 4 := by
  simp [PositiveQFIM.sloppiness, pauliXPositiveQFIM,
    qfim_ket0_pauliX2_eq_diagonal_four]

/-- In one parameter the paper's sloppiness AM--GM law is saturated. -/
theorem pauliXPositiveQFIM_sloppiness_law_saturated :
    pauliXPositiveQFIM.sloppiness ^ (((0 + 1 : ℕ) : ℝ)⁻¹) =
      pauliXPositiveQFIM.sldCramerRao / (0 + 1 : ℕ) := by
  rw [pauliXPositiveQFIM_sldCramerRao, pauliXPositiveQFIM_sloppiness]
  norm_num

end


end QuantumAlg
