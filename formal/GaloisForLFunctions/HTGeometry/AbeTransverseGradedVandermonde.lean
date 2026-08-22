import GaloisForLFunctions.HTGeometry.AbeGradedVandermonde
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Transverse graded Vandermonde blocks for Abe jets

The graded Vandermonde block for one distinguished jet coordinate tensors with any finite
transverse basis.  This isolates the finite local linear algebra needed after the analytic
coefficient sources have supplied the transverse packet.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Kronecker

noncomputable section

/-- The tensor product of the distinguished graded jet matrix with a finite transverse basis. -/
def abeTransverseGradedJetMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Nat}
    (c : Fin n → ℂ) (B : ℂ) : Matrix (ι × Fin n) (ι × Fin n) ℂ :=
  (1 : Matrix ι ι ℂ) ⊗ₖ abeGradedJetMatrix c B

/-- The tensor product of the distinguished jet-row normalizer with a transverse identity. -/
def abeTransverseGradedJetRowNormalizer {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Nat}
    (B : ℂ) : Matrix (ι × Fin n) (ι × Fin n) ℂ :=
  (1 : Matrix ι ι ℂ) ⊗ₖ abeGradedJetRowNormalizer B

/-- Row normalization removes the nonzero distinguished scale without changing the transverse
packet. -/
theorem abeTransverseGradedJetRowNormalizer_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Nat} (c : Fin n → ℂ) (B : ℂ) (hB : B ≠ 0) :
    abeTransverseGradedJetRowNormalizer (ι := ι) B *
        abeTransverseGradedJetMatrix (ι := ι) c B =
      abeTransverseGradedJetMatrix (ι := ι) c 1 := by
  change ((1 : Matrix ι ι ℂ) ⊗ₖ abeGradedJetRowNormalizer B) *
      ((1 : Matrix ι ι ℂ) ⊗ₖ abeGradedJetMatrix c B) =
    (1 : Matrix ι ι ℂ) ⊗ₖ abeGradedJetMatrix c 1
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, abeGradedJetRowNormalizer_mul c hB]

/-- A finite transverse tensor block is nonsingular whenever its one-variable graded Vandermonde
factor is nonsingular. -/
theorem abeTransverseGradedJetMatrix_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Nat} (c : Fin n → ℂ) (B : ℂ) (hc : Function.Injective c) (hB : B ≠ 0) :
    (abeTransverseGradedJetMatrix (ι := ι) c B).det ≠ 0 := by
  have hdet_one : (1 : Matrix ι ι ℂ).det = 1 := Matrix.det_one
  rw [abeTransverseGradedJetMatrix, Matrix.det_kronecker, hdet_one, one_pow, one_mul]
  exact pow_ne_zero _ (abeGradedJetMatrix_det_ne_zero c B hc hB)

end

end GaloisForLFunctions.HTGeometry
