import GaloisForLFunctions.HTGeometry.PauliCommutator
import GaloisForLFunctions.QuantumAlg.Util.QuantumFisher
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Kennard uncertainty for finite matrix mechanics

This module turns the quantum-covariance infrastructure into a closed finite-dimensional
Kennard inequality. Normalization and Hermiticity are carried by data rather than theorem
hypotheses. The result applies directly to every finite Pauli string in the corpus.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite matrix-mechanics state carrying its normalization law. -/
structure MatrixMechanicsState (n : Type*) [Fintype n] where
  vector : n → ℂ
  normalized : star vector ⬝ᵥ vector = 1

/-- A finite observable carrying its Hermiticity law. -/
structure HermitianObservable (n : Type*) [Fintype n] where
  matrix : Matrix n n ℂ
  hermitian : matrixᴴ = matrix

/-- Imaginary centered correlation is controlled by diagonal quantum covariance. -/
private theorem centered_im_sq_le_covariance_product
    {n : Type*} [Fintype n] (ψ : MatrixMechanicsState n)
    (A B : HermitianObservable n) :
    (star (QuantumAlg.centered ψ.vector A.matrix) ⬝ᵥ
        QuantumAlg.centered ψ.vector B.matrix).im ^ (2 : ℕ) ≤
      QuantumAlg.qCov ψ.vector A.matrix A.matrix *
        QuantumAlg.qCov ψ.vector B.matrix B.matrix := by
  let u := QuantumAlg.centered ψ.vector A.matrix
  let v := QuantumAlg.centered ψ.vector B.matrix
  have hcs := inner_mul_inner_self_le
    (𝕜 := ℂ) (WithLp.toLp 2 u) (WithLp.toLp 2 v)
  have him : (star u ⬝ᵥ v).im ^ (2 : ℕ) ≤ Complex.normSq (star u ⬝ᵥ v) := by
    simpa [pow_two] using Complex.im_sq_le_normSq (star u ⬝ᵥ v)
  have hnormprod :
      ‖v ⬝ᵥ star u‖ * ‖u ⬝ᵥ star v‖ = Complex.normSq (star u ⬝ᵥ v) := by
    have hleft : ‖v ⬝ᵥ star u‖ = ‖star u ⬝ᵥ v‖ := by
      rw [dotProduct_comm]
    have hright : ‖u ⬝ᵥ star v‖ = ‖star u ⬝ᵥ v‖ := by
      rw [dotProduct_comm, star_dotProduct, norm_star]
    rw [hleft, hright, Complex.norm_mul_self_eq_normSq]
  have hnorm : Complex.normSq (star u ⬝ᵥ v) ≤
      (star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re := by
    calc
      Complex.normSq (star u ⬝ᵥ v) =
          ‖v ⬝ᵥ star u‖ * ‖u ⬝ᵥ star v‖ := hnormprod.symm
      _ ≤ (u ⬝ᵥ star u).re * (v ⬝ᵥ star v).re := by
        simpa only [EuclideanSpace.inner_toLp_toLp,
          RCLike.re_eq_complex_re] using hcs
      _ = (star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re := by
        rw [dotProduct_comm u (star u), dotProduct_comm v (star v)]
  calc
    (star (QuantumAlg.centered ψ.vector A.matrix) ⬝ᵥ
        QuantumAlg.centered ψ.vector B.matrix).im ^ (2 : ℕ) =
        (star u ⬝ᵥ v).im ^ (2 : ℕ) := rfl
    _ ≤ Complex.normSq (star u ⬝ᵥ v) := him
    _ ≤ (star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re := hnorm
    _ = QuantumAlg.qCov ψ.vector A.matrix A.matrix *
        QuantumAlg.qCov ψ.vector B.matrix B.matrix := by
      rw [QuantumAlg.qCov_eq_inner_re ψ.normalized A.hermitian,
        QuantumAlg.qCov_eq_inner_re ψ.normalized B.hermitian]

/-- **Finite matrix Kennard inequality.** The squared imaginary expectation of the commutator is
at most four times the product of the two quantum variances. -/
theorem matrixMechanics_kennard
    {n : Type*} [Fintype n] (ψ : MatrixMechanicsState n)
    (A B : HermitianObservable n) :
    (QuantumAlg.expval ψ.vector (A.matrix * B.matrix - B.matrix * A.matrix)).im ^ (2 : ℕ) ≤
      4 * QuantumAlg.qCov ψ.vector A.matrix A.matrix *
        QuantumAlg.qCov ψ.vector B.matrix B.matrix := by
  let z := star (QuantumAlg.centered ψ.vector A.matrix) ⬝ᵥ
    QuantumAlg.centered ψ.vector B.matrix
  have hAB := QuantumAlg.centered_inner ψ.normalized A.hermitian
    (B := B.matrix)
  have hBA := QuantumAlg.centered_inner ψ.normalized B.hermitian
    (B := A.matrix)
  have hswap : star (QuantumAlg.centered ψ.vector B.matrix) ⬝ᵥ
      QuantumAlg.centered ψ.vector A.matrix = star z := by
    exact star_dotProduct _ _
  have hcomm :
      (QuantumAlg.expval ψ.vector (A.matrix * B.matrix - B.matrix * A.matrix)).im =
        2 * z.im := by
    rw [show A.matrix * B.matrix - B.matrix * A.matrix =
      A.matrix * B.matrix + (-1 : ℂ) • (B.matrix * A.matrix) by module]
    rw [QuantumAlg.expval_add, QuantumAlg.expval_smul]
    simp only [smul_eq_mul, neg_one_mul]
    change (QuantumAlg.expval ψ.vector (A.matrix * B.matrix) -
      QuantumAlg.expval ψ.vector (B.matrix * A.matrix)).im = 2 * z.im
    rw [Complex.sub_im]
    have hABim := congrArg Complex.im hAB
    have hBAim := congrArg Complex.im hBA
    rw [hswap, Complex.star_def, Complex.conj_im] at hBAim
    dsimp [z] at hABim hBAim ⊢
    have hAreal : (QuantumAlg.expval ψ.vector A.matrix).im = 0 :=
      Complex.conj_eq_iff_im.mp
        (QuantumAlg.expval_conj_self_of_isHermitian A.hermitian)
    have hBreal : (QuantumAlg.expval ψ.vector B.matrix).im = 0 :=
      Complex.conj_eq_iff_im.mp
        (QuantumAlg.expval_conj_self_of_isHermitian B.hermitian)
    simp only [Complex.mul_im, hAreal, hBreal,
      mul_zero, zero_mul, add_zero] at hABim hBAim
    linarith
  rw [hcomm]
  nlinarith [centered_im_sq_le_covariance_product ψ A B]

/-- Every corpus Pauli string is a packaged Hermitian observable. -/
def finitePauliObservable
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) : HermitianObservable (FiniteQubitConfiguration σ) where
  matrix := finitePauliMatrix P
  hermitian := finitePauliMatrix_isHermitian P

/-- Kennard uncertainty for every pair of finite Pauli strings. -/
theorem finitePauli_kennard
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : MatrixMechanicsState (FiniteQubitConfiguration σ))
    (P Q : σ → Option (Fin 3)) :
    (QuantumAlg.expval ψ.vector
      (finitePauliMatrix P * finitePauliMatrix Q -
        finitePauliMatrix Q * finitePauliMatrix P)).im ^ (2 : ℕ) ≤
      4 * QuantumAlg.qCov ψ.vector (finitePauliMatrix P) (finitePauliMatrix P) *
        QuantumAlg.qCov ψ.vector (finitePauliMatrix Q) (finitePauliMatrix Q) :=
  matrixMechanics_kennard ψ (finitePauliObservable P) (finitePauliObservable Q)

/-- Pauli variance is `1 - mean²`, because every Pauli string is an involution. -/
theorem finitePauli_variance_eq_one_sub_mean_sq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : MatrixMechanicsState (FiniteQubitConfiguration σ))
    (P : σ → Option (Fin 3)) :
    QuantumAlg.qCov ψ.vector (finitePauliMatrix P) (finitePauliMatrix P) =
      1 - (QuantumAlg.expval ψ.vector (finitePauliMatrix P)).re ^ (2 : ℕ) := by
  rw [QuantumAlg.qCov, finitePauliMatrix_mul_self]
  have hone : QuantumAlg.expval ψ.vector
      (1 : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) = 1 := by
    simpa [QuantumAlg.expval] using ψ.normalized
  rw [hone]
  norm_num
  ring

/-- Pauli Kennard inequality with both variances reduced to their exact involution form. -/
theorem finitePauli_kennard_involution_form
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : MatrixMechanicsState (FiniteQubitConfiguration σ))
    (P Q : σ → Option (Fin 3)) :
    (QuantumAlg.expval ψ.vector
      (finitePauliMatrix P * finitePauliMatrix Q -
        finitePauliMatrix Q * finitePauliMatrix P)).im ^ (2 : ℕ) ≤
      4 * (1 - (QuantumAlg.expval ψ.vector (finitePauliMatrix P)).re ^ (2 : ℕ)) *
        (1 - (QuantumAlg.expval ψ.vector (finitePauliMatrix Q)).re ^ (2 : ℕ)) := by
  simpa only [finitePauli_variance_eq_one_sub_mean_sq] using finitePauli_kennard ψ P Q

/-- Kennard bound after replacing the Pauli commutator by its exact phase-times-Pauli product. -/
theorem finitePauli_phase_kennard
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : MatrixMechanicsState (FiniteQubitConfiguration σ))
    (P Q : σ → Option (Fin 3)) :
    (QuantumAlg.expval ψ.vector
      (((∏ s, optPhase (P s) (Q s)) - ∏ s, optPhase (Q s) (P s)) •
        finitePauliMatrix fun s => optMul (P s) (Q s))).im ^ (2 : ℕ) ≤
      4 * (1 - (QuantumAlg.expval ψ.vector (finitePauliMatrix P)).re ^ (2 : ℕ)) *
        (1 - (QuantumAlg.expval ψ.vector (finitePauliMatrix Q)).re ^ (2 : ℕ)) := by
  rw [← finitePauliMatrix_commutator]
  exact finitePauli_kennard_involution_form ψ P Q

/-- Single-qubit `X`/`Z` specialization of finite matrix Kennard uncertainty. -/
theorem singleQubit_pauliXZ_kennard (ψ : MatrixMechanicsState Bool) :
    (QuantumAlg.expval ψ.vector
      (finiteQubitPauli 0 * finiteQubitPauli 2 -
        finiteQubitPauli 2 * finiteQubitPauli 0)).im ^ (2 : ℕ) ≤
      4 * QuantumAlg.qCov ψ.vector (finiteQubitPauli 0) (finiteQubitPauli 0) *
        QuantumAlg.qCov ψ.vector (finiteQubitPauli 2) (finiteQubitPauli 2) :=
  matrixMechanics_kennard ψ
    ⟨finiteQubitPauli 0, finiteQubitPauli_isHermitian 0⟩
    ⟨finiteQubitPauli 2, finiteQubitPauli_isHermitian 2⟩

end

end GaloisForLFunctions.HTGeometry
