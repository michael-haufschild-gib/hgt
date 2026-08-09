import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw

/-!
# The Pauli strings are a complex basis of the qubit matrix algebra

The literal finite-qubit Pauli strings are complex-linearly independent, and there are exactly as
many of them as the complex dimension of the matrix algebra, so they are a complex basis and their
span is everything.

The corpus already had the real Hermitian basis; this is the complex statement, which is what a
character decomposition of the whole matrix algebra needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

noncomputable section

/-- Pauli-label cardinality equals the complex dimension of the matrix algebra. -/
theorem finitePauliLabel_card_eq_matrix_finrank (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Fintype.card (σ → Option (Fin 3)) =
      Module.finrank ℂ
        (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) := by
  rw [Module.finrank_matrix]
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_bool]
  rw [← mul_pow]
  norm_num

/-- **The literal Pauli strings are a complex basis of the qubit matrix algebra.** -/
def finitePauliMatrixBasis (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Basis (σ → Option (Fin 3)) ℂ
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (finitePauliMatrix_linearIndependent (σ := σ))
    (finitePauliLabel_card_eq_matrix_finrank σ)

theorem coe_finitePauliMatrixBasis (σ : Type*) [Fintype σ] [DecidableEq σ] :
    ⇑(finitePauliMatrixBasis σ) = finitePauliMatrix :=
  coe_basisOfLinearIndependentOfCardEqFinrank
    (finitePauliMatrix_linearIndependent (σ := σ))
    (finitePauliLabel_card_eq_matrix_finrank σ)

@[simp] theorem finitePauliMatrixBasis_apply {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finitePauliMatrixBasis σ P = finitePauliMatrix P :=
  congrFun (coe_finitePauliMatrixBasis σ) P

/-- **The Pauli strings span the qubit matrix algebra over the complex numbers.** -/
theorem span_range_finitePauliMatrix (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Submodule.span ℂ
        (Set.range (finitePauliMatrix :
          (σ → Option (Fin 3)) →
            Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)) = ⊤ := by
  have h := (finitePauliMatrixBasis σ).span_eq
  rwa [coe_finitePauliMatrixBasis] at h

end

end GaloisForLFunctions.HTGeometry
