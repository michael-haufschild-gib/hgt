import Mathlib

/-!
# Universal matrix permanent

Minimal universal permanent API used by the HGT falling-factorial specialization.
-/

noncomputable section

namespace PermanentRollout

open scoped BigOperators

/-- Universal permanent polynomial in the entries of an `n × n` matrix. -/
noncomputable def permanent (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  Matrix.permanent (fun row column => MvPolynomial.X (row, column))

/-- Evaluating the universal permanent polynomial gives the matrix permanent. -/
theorem permanent_aeval_eq_matrix_permanent
    {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ)) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => A ij.1 ij.2)
      (permanent n) = Matrix.permanent A := by
  classical
  simp only [permanent, Matrix.permanent, map_sum, map_prod,
    MvPolynomial.aeval_X]

end PermanentRollout
