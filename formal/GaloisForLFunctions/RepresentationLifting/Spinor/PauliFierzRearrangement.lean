import GaloisForLFunctions.HTGeometry.PauliParseval

/-!
# Fierz rearrangement in every finite-qubit matrix algebra

Pauli completeness exchanges the pairings of four spinors. The same identity
rearranges two traces with arbitrary matrix insertions. All coefficients and
normalizations follow from the existing literal Pauli basis.
-/

open scoped BigOperators
open Matrix
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.RepresentationLifting.Spinor
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Trace-dual completeness for the literal Pauli matrices. -/
theorem pauli_trace_completeness
    (M : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    (∑ P, Matrix.trace (star (finitePauliMatrix P) * M) • finitePauliMatrix P) =
      (2 : ℂ)^Fintype.card σ • M := by
  simp only [trace_star_pauli_mul, mul_smul, ← Finset.smul_sum, sum_pauliCoeff_smul]

/-- Bilinear completeness, the matrix form of Fierz rearrangement. -/
theorem pauli_fierz_trace
    (M N : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    (∑ P, Matrix.trace (star (finitePauliMatrix P) * M) *
      Matrix.trace (finitePauliMatrix P * N)) =
      (2 : ℂ)^Fintype.card σ * Matrix.trace (M*N) := by
  have h := congrArg (fun A => Matrix.trace (A*N)) (pauli_trace_completeness M)
  simpa only [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul] using h

private lemma trace_mul_outer {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (u v : ι → ℂ) :
    Matrix.trace (M * Matrix.vecMulVec u v) = v ⬝ᵥ (M *ᵥ u) := by
  change (∑ i, ∑ j, M i j * (u j * v i)) = ∑ i, v i * ∑ j, M i j * u j
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Hermitian pairing of two spinor columns. -/
def spinorPairing {ι : Type*} [Fintype ι] (v u : ι → ℂ) : ℂ := (star v) ⬝ᵥ u

/-- Four-spinor rearrangement, with the exact dimension factor for any number of qubits. -/
theorem pauli_fierz_spinors (u v x y : FiniteQubitConfiguration σ → ℂ) :
    (∑ P, spinorPairing x (star (finitePauliMatrix P) *ᵥ y) *
      spinorPairing v (finitePauliMatrix P *ᵥ u)) =
      (2 : ℂ)^Fintype.card σ * (spinorPairing x u * spinorPairing v y) := by
  have h := pauli_fierz_trace (Matrix.vecMulVec y (star x)) (Matrix.vecMulVec u (star v))
  simp only [trace_mul_outer] at h
  unfold spinorPairing
  rw [h]
  congr 1
  change (∑ i, star (v i) * ∑ j, (y i * star (x j)) * u j) = _
  have he (i : FiniteQubitConfiguration σ) :
      (∑ j, (y i * star (x j)) * u j) = y i * ((star x) ⬝ᵥ u) := by
    simp only [dotProduct, Finset.mul_sum, Pi.star_apply, mul_assoc]
  simp_rw [he, ← mul_assoc]
  rw [← Finset.sum_mul]
  exact mul_comm _ _

/-- Inserting arbitrary matrices gives the crossed trace identity. -/
theorem pauli_fierz_insertions
    (A B C D : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    (∑ P, Matrix.trace (C * star (finitePauliMatrix P) * D) *
      Matrix.trace (A * finitePauliMatrix P * B)) =
      (2 : ℂ)^Fintype.card σ * Matrix.trace (D*C*B*A) := by
  have h := pauli_fierz_trace (D*C) (B*A)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro P _
    congr 1 <;> rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc]

#print axioms pauli_trace_completeness
#print axioms pauli_fierz_trace
#print axioms pauli_fierz_spinors
#print axioms pauli_fierz_insertions
end
end GaloisForLFunctions.RepresentationLifting.Spinor
