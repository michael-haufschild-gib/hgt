import GaloisForLFunctions.HTGeometry.PauliHilbertSchmidtNorm
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliComplexBasis

/-!
# Parseval for the Pauli basis

The Pauli strings are an orthogonal basis of the qubit matrix algebra for the Hilbert–Schmidt
pairing, with every string of squared length the Hilbert space dimension.  Expanding a matrix in
that basis therefore expresses the sum of the squared moduli of its Pauli coefficients through its
Frobenius norm: the sum of `|Tr(P†A)|²` over all Pauli strings is the dimension times the Frobenius
square of `A`.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The Pauli coefficient vector of a matrix. -/
def pauliCoeff (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    (σ → Option (Fin 3)) → ℂ :=
  fun P => (finitePauliMatrixBasis σ).repr A P

theorem sum_pauliCoeff_smul (A : Matrix (FiniteQubitConfiguration σ)
    (FiniteQubitConfiguration σ) ℂ) :
    (∑ P, pauliCoeff A P • finitePauliMatrix P) = A := by
  classical
  have h := (finitePauliMatrixBasis σ).sum_repr A
  simpa [pauliCoeff, finitePauliMatrixBasis_apply] using h

/-- The Hilbert–Schmidt pairing recovers the Pauli coefficient. -/
theorem trace_star_pauli_mul (A : Matrix (FiniteQubitConfiguration σ)
    (FiniteQubitConfiguration σ) ℂ) (Q : σ → Option (Fin 3)) :
    Matrix.trace (star (finitePauliMatrix Q) * A) =
      (2 : ℂ) ^ Fintype.card σ * pauliCoeff A Q := by
  classical
  conv_lhs => rw [← sum_pauliCoeff_smul A]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  have hterm : ∀ P : σ → Option (Fin 3),
      Matrix.trace (star (finitePauliMatrix Q) * (pauliCoeff A P • finitePauliMatrix P)) =
        pauliCoeff A P * (if Q = P then (2 : ℂ) ^ Fintype.card σ else 0) := by
    intro P
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_star_finitePauliMatrix_mul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun P _ => hterm P]
  rw [Finset.sum_eq_single Q]
  · rw [if_pos rfl]
    ring
  · intro P _ hP
    rw [if_neg (fun h => hP h.symm), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ Q) hcon

/-- **Pauli–Parseval.** -/
theorem sum_normSq_trace_star_pauli_mul (A : Matrix (FiniteQubitConfiguration σ)
    (FiniteQubitConfiguration σ) ℂ) :
    (∑ P : σ → Option (Fin 3), ‖Matrix.trace (star (finitePauliMatrix P) * A)‖ ^ 2) =
      2 ^ Fintype.card σ * frobSq A := by
  classical
  have hfrob : frobSq A = 2 ^ Fintype.card σ * ∑ P, ‖pauliCoeff A P‖ ^ 2 := by
    conv_lhs => rw [← sum_pauliCoeff_smul A]
    exact frobSq_pauliCombination (pauliCoeff A)
  have hterm : ∀ P : σ → Option (Fin 3),
      ‖Matrix.trace (star (finitePauliMatrix P) * A)‖ ^ 2 =
        (2 : ℝ) ^ Fintype.card σ * ((2 : ℝ) ^ Fintype.card σ * ‖pauliCoeff A P‖ ^ 2) := by
    intro P
    rw [trace_star_pauli_mul, norm_mul, mul_pow]
    have hnorm : ‖(2 : ℂ) ^ Fintype.card σ‖ = (2 : ℝ) ^ Fintype.card σ := by
      rw [norm_pow]
      norm_num
    rw [hnorm]
    ring
  rw [Finset.sum_congr rfl fun P _ => hterm P, ← Finset.mul_sum, hfrob, ← Finset.mul_sum]

end GaloisForLFunctions.HTGeometry
