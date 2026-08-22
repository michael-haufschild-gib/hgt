import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Graded Vandermonde blocks for Abe damping

Distinct damping speeds turn the successive jets of one local exponential
coordinate into a Vandermonde matrix.  This is the finite algebraic core of
the graded-determinant route: its leading parameter coefficient is nonzero,
so only a normalized determinant limit is needed from the Poincaré tail.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The jet matrix of exponential damping columns with speeds `c` at parameter `B`.
Row `i` is the speed `c i`; column `j` is the jet order `j`. -/
def abeGradedVandermonde {n : ℕ} (c : Fin n → ℂ) (B : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vandermonde fun i ↦ c i * B

@[simp]
theorem abeGradedVandermonde_apply {n : ℕ} (c : Fin n → ℂ) (B : ℂ)
    (i j : Fin n) :
    abeGradedVandermonde c B i j = (c i * B) ^ (j : ℕ) :=
  rfl

/-- Nonzero parameter scaling preserves distinct damping speeds. -/
theorem Function.Injective.complex_mul_right {n : ℕ} {c : Fin n → ℂ} {B : ℂ}
    (hc : Function.Injective c) (hB : B ≠ 0) :
    Function.Injective fun i ↦ c i * B := by
  intro i j hij
  apply hc
  exact mul_right_cancel₀ hB hij

/-- **Graded damping Vandermonde.**  Distinct nonzero-speed columns have an invertible
finite jet matrix at every nonzero damping parameter. -/
theorem abeGradedVandermonde_det_ne_zero {n : ℕ} (c : Fin n → ℂ) (B : ℂ)
    (hc : Function.Injective c) (hB : B ≠ 0) :
    (abeGradedVandermonde c B).det ≠ 0 := by
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (Function.Injective.complex_mul_right hc hB)

/-- The same block in the evaluation-matrix orientation: rows are jet orders
and columns are damping speeds. -/
def abeGradedJetMatrix {n : ℕ} (c : Fin n → ℂ) (B : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (abeGradedVandermonde c B).transpose

/-- The row normalization which removes the degree of each jet row. -/
def abeGradedJetRowNormalizer {n : ℕ} (B : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j ↦ B⁻¹ ^ (j : ℕ)

/-- **Exact graded normalization.**  Degree-`j` row normalization changes the
jet matrix at any nonzero parameter to its unit-parameter Vandermonde block. -/
theorem abeGradedJetRowNormalizer_mul {n : ℕ} (c : Fin n → ℂ) {B : ℂ}
    (hB : B ≠ 0) :
    abeGradedJetRowNormalizer B * abeGradedJetMatrix c B =
      abeGradedJetMatrix c 1 := by
  ext i j
  rw [abeGradedJetRowNormalizer, abeGradedJetMatrix, Matrix.diagonal_mul,
    Matrix.transpose_apply, abeGradedVandermonde_apply]
  change B⁻¹ ^ (i : ℕ) * (c j * B) ^ (i : ℕ) = (c j * 1) ^ (i : ℕ)
  rw [mul_pow]
  calc
    B⁻¹ ^ (i : ℕ) * (c j ^ (i : ℕ) * B ^ (i : ℕ)) =
        c j ^ (i : ℕ) * (B⁻¹ ^ (i : ℕ) * B ^ (i : ℕ)) := by ring
    _ = c j ^ (i : ℕ) * ((B⁻¹ * B) ^ (i : ℕ)) := by rw [mul_pow]
    _ = c j ^ (i : ℕ) * 1 := by rw [inv_mul_cancel₀ hB, one_pow]
    _ = (c j * 1) ^ (i : ℕ) := by simp

/-- The jet-oriented graded block is invertible for distinct speeds and a
nonzero parameter. -/
theorem abeGradedJetMatrix_det_ne_zero {n : ℕ} (c : Fin n → ℂ) (B : ℂ)
    (hc : Function.Injective c) (hB : B ≠ 0) :
    (abeGradedJetMatrix c B).det ≠ 0 := by
  rw [abeGradedJetMatrix, Matrix.det_transpose]
  exact abeGradedVandermonde_det_ne_zero c B hc hB

end

end GaloisForLFunctions.HTGeometry
