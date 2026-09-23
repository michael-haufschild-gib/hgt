import GaloisForLFunctions.HTGeometry.SpectralCollisionFunctional
import GaloisForLFunctions.HTGeometry.EnergyMatchedEigenframeSourceMemory

/-!
# Hilbert–Schmidt size of a Pauli combination

The squared Hilbert–Schmidt size of a matrix is the trace of its Gram square, and the Pauli words
are orthogonal for that pairing with common squared size the Hilbert dimension.  The squared
Hilbert–Schmidt size of a Pauli combination is therefore the dimension times its squared
coefficient sum.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Frobenius

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The squared Hilbert–Schmidt size is the trace of the Gram square. -/
theorem ofReal_frobSq_eq_trace (M : Matrix α α ℂ) :
    ((frobSq M : ℝ) : ℂ) = Matrix.trace (star M * M) := by
  classical
  have hpt : ∀ z : ℂ, ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) = star z * z := by
    intro z
    change ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) = (starRingEnd ℂ) z * z
    rw [Complex.sq_norm, ← Complex.mul_conj]
    ring
  rw [frobSq, Complex.ofReal_sum, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun y _ => hpt (M x y)

end Frobenius

section Pauli

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Hilbert–Schmidt size of a Pauli combination.** -/
theorem frobSq_pauliCombination (J : (σ → Option (Fin 3)) → ℂ) :
    frobSq (∑ P, J P • finitePauliMatrix P) =
      2 ^ Fintype.card σ * ∑ P, ‖J P‖ ^ (2 : ℕ) := by
  classical
  have hcast : ((frobSq (∑ P, J P • finitePauliMatrix P) : ℝ) : ℂ) =
      ((2 ^ Fintype.card σ * ∑ P, ‖J P‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [ofReal_frobSq_eq_trace, star_sum, Finset.sum_mul, Matrix.trace_sum]
    have hterm : ∀ P : σ → Option (Fin 3),
        Matrix.trace (star (J P • finitePauliMatrix P) *
            ∑ Q, J Q • finitePauliMatrix Q) =
          ((‖J P‖ ^ (2 : ℕ) : ℝ) : ℂ) * (2 : ℂ) ^ Fintype.card σ := by
      intro P
      rw [Finset.mul_sum, Matrix.trace_sum]
      rw [Finset.sum_eq_single P]
      · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
          trace_star_finitePauliMatrix_mul P P, if_pos rfl]
        simp only [smul_eq_mul, RCLike.star_def]
        rw [Complex.sq_norm, ← Complex.mul_conj]
        ring
      · intro Q _ hQP
        rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
          trace_star_finitePauliMatrix_mul P Q, if_neg (Ne.symm hQP)]
        simp
      · intro hcon
        exact absurd (Finset.mem_univ P) hcon
    rw [Finset.sum_congr rfl fun P (_ : P ∈ Finset.univ) => hterm P, ← Finset.sum_mul]
    push_cast
    ring
  exact_mod_cast hcast

end Pauli

end GaloisForLFunctions.HTGeometry
