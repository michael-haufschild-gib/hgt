import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalAmplitude
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Tensor Kraus infrastructure for composite dissipative dynamics

To apply the conservative–dissipative mechanism of arXiv:2609.04530 to composite
quantum carriers, this module transports Kronecker products to the corpus's
existing `Fin`-indexed matrix spaces. Multiplication, adjoints, traces, scalar
transport, finite sums, and the complete matrix-unit expansion are proved for
unrestricted matrices. The product constructor derives Kraus completeness from
existing normalized channel representations; it postulates no channel laws.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Kronecker product in the existing `Fin`-indexed quantum carriers. -/
def finiteSpinTensorMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (m * n)) (Fin (m * n)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv (A ⊗ₖ B)

/-- Tensoring respects multiplication on arbitrary raw matrices. -/
theorem finiteSpinTensorMatrix_mul {m n : ℕ} (A C : Matrix (Fin m) (Fin m) ℂ)
    (B D : Matrix (Fin n) (Fin n) ℂ) :
    finiteSpinTensorMatrix (A * C) (B * D) = finiteSpinTensorMatrix A B * finiteSpinTensorMatrix C D := by
  unfold finiteSpinTensorMatrix
  rw [Matrix.mul_kronecker_mul, map_mul]

/-- Adjoint compatibility for the same finite carriers. -/
theorem finiteSpinTensorMatrix_conjTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    (finiteSpinTensorMatrix A B)ᴴ = finiteSpinTensorMatrix Aᴴ Bᴴ := by
  simp only [finiteSpinTensorMatrix, Matrix.coe_reindexAlgEquiv,
    Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker]

/-- Tensor identities remain literal identities after index transport. -/
theorem finiteSpinTensorMatrix_one (m n : ℕ) :
    finiteSpinTensorMatrix (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [finiteSpinTensorMatrix, Matrix.one_kronecker_one, map_one]

/-- Scalar transport in the first tensor factor. -/
theorem finiteSpinTensorMatrix_smul_left {m n : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    finiteSpinTensorMatrix (c • A) B = c • finiteSpinTensorMatrix A B := by
  unfold finiteSpinTensorMatrix
  rw [Matrix.smul_kronecker, map_smul]

/-- Scalar transport in the second tensor factor. -/
theorem finiteSpinTensorMatrix_smul_right {m n : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    finiteSpinTensorMatrix A (c • B) = c • finiteSpinTensorMatrix A B := by
  unfold finiteSpinTensorMatrix
  rw [Matrix.kronecker_smul, map_smul]

/-- Finite sums in the first tensor factor. -/
theorem finiteSpinTensorMatrix_sum_left {m n : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    finiteSpinTensorMatrix (∑ a, A a) B = ∑ a, finiteSpinTensorMatrix (A a) B := by
  ext i j
  simp [finiteSpinTensorMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap, Matrix.sum_apply, Finset.sum_mul]

/-- Finite sums in the second tensor factor. -/
theorem finiteSpinTensorMatrix_sum_right {m n : ℕ} {κ : Type*} [Fintype κ]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : κ → Matrix (Fin n) (Fin n) ℂ) :
    finiteSpinTensorMatrix A (∑ b, B b) = ∑ b, finiteSpinTensorMatrix A (B b) := by
  ext i j
  simp [finiteSpinTensorMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap, Matrix.sum_apply, Finset.mul_sum]

/-- Multiplicative trace law in the corpus's native finite-dimensional carrier. -/
theorem finiteSpinTensorMatrix_trace {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (finiteSpinTensorMatrix A B) = Matrix.trace A * Matrix.trace B := by
  rw [← Matrix.trace_kronecker]
  change (∑ i : Fin (m * n), (A ⊗ₖ B) (finProdFinEquiv.symm i) (finProdFinEquiv.symm i)) =
    ∑ i : Fin m × Fin n, (A ⊗ₖ B) i i
  exact finProdFinEquiv.symm.sum_comp (fun i : Fin m × Fin n => (A ⊗ₖ B) i i)

/-- The tensor Kraus sum factorizes on every simple tensor, without normalization assumptions. -/
theorem finiteSpinTensorMatrix_kraus_sum {m n : ℕ} {κ η : Type*} [Fintype κ] [Fintype η]
    (K : κ → Matrix (Fin m) (Fin m) ℂ) (L : η → Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (∑ e : κ × η, finiteSpinTensorMatrix (K e.1) (L e.2) * finiteSpinTensorMatrix A B *
      (finiteSpinTensorMatrix (K e.1) (L e.2))ᴴ) =
      finiteSpinTensorMatrix (∑ a, K a * A * (K a)ᴴ) (∑ b, L b * B * (L b)ᴴ) := by
  simp only [Fintype.sum_prod_type, finiteSpinTensorMatrix_conjTranspose, ← finiteSpinTensorMatrix_mul]
  simp_rw [← finiteSpinTensorMatrix_sum_right]
  rw [← finiteSpinTensorMatrix_sum_left]

/-- Elementary tensors are literal matrix units in the combined carrier. -/
theorem finiteSpinTensorMatrix_single {m n : ℕ} (i j : Fin m) (k l : Fin n) (c : ℂ) :
    finiteSpinTensorMatrix (Matrix.single i j c) (Matrix.single k l (1 : ℂ)) =
      Matrix.single (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) c := by
  simp only [finiteSpinTensorMatrix, Matrix.single_kronecker_single, mul_one,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv, Equiv.symm_symm]

/-- Every combined-carrier matrix has an exact finite expansion in elementary tensor matrices. -/
theorem finiteSpinTensorMatrix_expansion {m n : ℕ} (ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    ρ = ∑ i : Fin m × Fin n, ∑ j : Fin m × Fin n,
      finiteSpinTensorMatrix (Matrix.single i.1 j.1 (ρ (finProdFinEquiv i) (finProdFinEquiv j)))
        (Matrix.single i.2 j.2 (1 : ℂ)) := by
  simp only [finiteSpinTensorMatrix_single, Prod.mk.eta]
  symm
  calc
    _ = ∑ i : Fin m × Fin n, ∑ j : Fin (m * n),
        Matrix.single (finProdFinEquiv i) j (ρ (finProdFinEquiv i) j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact finProdFinEquiv.sum_comp (fun j : Fin (m * n) => Matrix.single (finProdFinEquiv i) j (ρ (finProdFinEquiv i) j))
    _ = ∑ i : Fin (m * n), ∑ j : Fin (m * n), Matrix.single i j (ρ i j) :=
      finProdFinEquiv.sum_comp (fun i : Fin (m * n) => ∑ j : Fin (m * n), Matrix.single i j (ρ i j))
    _ = ρ := Matrix.sum_sum_single ρ

/-- Construct the product of existing normalized Kraus representations, proving completeness from their laws. -/
def rectangularSpinKrausTensor {m n : ℕ} {κ η : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]
    (Phi : FiniteRectangularKrausChannel m m κ) (Psi : FiniteRectangularKrausChannel n n η) :
    FiniteRectangularKrausChannel (m * n) (m * n) (κ × η) where
  operator e := finiteSpinTensorMatrix (Phi.operator e.1) (Psi.operator e.2)
  completeness := by
    simp only [Fintype.sum_prod_type, finiteSpinTensorMatrix_conjTranspose, ← finiteSpinTensorMatrix_mul]
    simp_rw [← finiteSpinTensorMatrix_sum_right]
    rw [← finiteSpinTensorMatrix_sum_left, Phi.completeness, Psi.completeness, finiteSpinTensorMatrix_one]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
