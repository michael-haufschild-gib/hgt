import GaloisForLFunctions.HTGeometry.MatrixWignerSmithConstantGauge
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Hermitian Wigner--Smith matrices and real delay reporters

On a unitary locus, if the differential commutes with the star operation and
the chosen imaginary unit is anti-self-adjoint, the Wigner--Smith matrix is
Hermitian.  Every channel quadratic form is consequently self-adjoint.
-/

open scoped Differential Matrix

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

universe u

/-- Entrywise differentiation satisfies the matrix Leibniz rule. -/
theorem matrixDifferential_mul
    {E : Type u} [Field E] [Differential E] {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    matrixDifferential (A * B) =
      matrixDifferential A * B + A * matrixDifferential B := by
  ext a b
  rw [matrixDifferential, Matrix.mul_apply, map_sum]
  simp_rw [Derivation.leibniz]
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [matrixDifferential]
  ring

/-- The identity matrix has zero entrywise differential. -/
theorem matrixDifferential_one
    {E : Type u} [Field E] [Differential E] {n : ℕ} :
    matrixDifferential (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) = 0 := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [matrixDifferential]
  · simp [matrixDifferential, h]

/-- A star-compatible differential commutes with conjugate transpose. -/
theorem matrixDifferential_conjTranspose
    {E : Type u} [Field E] [StarRing E] [Differential E] {n : ℕ}
    (hstar : ∀ x : E, star x′ = (star x)′)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    matrixDifferential Sᴴ = (matrixDifferential S)ᴴ := by
  ext a b
  simp [matrixDifferential, hstar]

/-- On the unitary real locus, the algebraic Wigner--Smith matrix is Hermitian. -/
theorem matrixWignerSmith_isHermitian
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [StarRing E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hunit : Sᴴ * S = 1)
    (hstar : ∀ x : E, star x′ = (star x)′)
    (hιstar : star (algebraMap F E ι) = -algebraMap F E ι) :
    (matrixWignerSmith ι S).IsHermitian := by
  have hdiff := congrArg matrixDifferential hunit
  rw [matrixDifferential_mul, matrixDifferential_one,
    matrixDifferential_conjTranspose hstar] at hdiff
  have hskew : (Sᴴ * matrixDifferential S)ᴴ =
      -(Sᴴ * matrixDifferential S) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact eq_neg_of_add_eq_zero_left hdiff
  rw [Matrix.IsHermitian, matrixWignerSmith, Matrix.inv_eq_left_inv hunit]
  rw [Matrix.conjTranspose_smul, hskew, star_neg, hιstar]
  simp

/-- The scalar delay reported by a channel vector.  Normalization is not needed
for the reality statement. -/
def matrixDelayQuadratic
    {E : Type u} [Field E] [StarRing E] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (v : Fin (n + 1) → E) : E :=
  star v ⬝ᵥ (Q *ᵥ v)

/-- Every quadratic reporter of a Hermitian matrix is self-adjoint. -/
theorem matrixDelayQuadratic_star_eq
    {E : Type u} [Field E] [StarRing E] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hQ : Q.IsHermitian) (v : Fin (n + 1) → E) :
    star (matrixDelayQuadratic Q v) = matrixDelayQuadratic Q v := by
  unfold matrixDelayQuadratic
  calc
    star (star v ⬝ᵥ Q *ᵥ v) = star (Q *ᵥ v) ⬝ᵥ v := by
      simpa using (Matrix.star_dotProduct_star (Q *ᵥ v) (star v)).symm
    _ = (star v ᵥ* Qᴴ) ⬝ᵥ v := by rw [Matrix.star_mulVec]
    _ = star v ⬝ᵥ Qᴴ *ᵥ v := by rw [Matrix.dotProduct_mulVec]
    _ = star v ⬝ᵥ Q *ᵥ v := by rw [hQ.eq]

/-- Every physical channel reporter of a unitary Wigner--Smith matrix is self-adjoint. -/
theorem matrixWignerSmith_delayQuadratic_star_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [StarRing E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hunit : Sᴴ * S = 1)
    (hstar : ∀ x : E, star x′ = (star x)′)
    (hιstar : star (algebraMap F E ι) = -algebraMap F E ι)
    (v : Fin (n + 1) → E) :
    star (matrixDelayQuadratic (matrixWignerSmith ι S) v) =
      matrixDelayQuadratic (matrixWignerSmith ι S) v :=
  matrixDelayQuadratic_star_eq _
    (matrixWignerSmith_isHermitian ι S hunit hstar hιstar) v

end

end GaloisForLFunctions.HTGeometry
