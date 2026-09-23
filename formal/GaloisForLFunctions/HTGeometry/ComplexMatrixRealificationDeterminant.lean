import GaloisForLFunctions.HTGeometry.ComplexHermitianRowRealification
import GaloisForLFunctions.HTGeometry.FiniteMatrixOrthogonalSumDeterminant

/-!
# Determinants of complex matrix realifications

The standard doubled-real block representation of a complex matrix is the restriction of its
complex-linear action to real scalars.  Restriction of scalars identifies its real determinant
with the real algebra norm of the complex determinant.  Conjugating to the row convention does
not change this determinant.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Classical Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Recombination of doubled real coordinates as a real-linear equivalence. -/
def complexOfDoubledRealLinearEquiv :
    (n ⊕ n → ℝ) ≃ₗ[ℝ] (n → ℂ) where
  toFun := complexOfDoubledReal
  invFun z
    | Sum.inl i => (z i).re
    | Sum.inr i => (z i).im
  left_inv x := by
    funext i
    rcases i with i | i <;> rfl
  right_inv z := by
    funext i
    exact Complex.ext rfl rfl
  map_add' x y := by
    funext i
    apply Complex.ext <;> rfl
  map_smul' c x := by
    funext i
    apply Complex.ext <;> simp [complexOfDoubledReal]

omit [DecidableEq n] in
/-- Doubled-real matrix multiplication is the restriction of complex matrix multiplication. -/
theorem complexOfDoubledRealLinearEquiv_realification_mulVec
    (A : Matrix n n ℂ) (x : n ⊕ n → ℝ) :
    complexOfDoubledRealLinearEquiv
        ((complexMatrixRealification A).mulVec x) =
      A.mulVec (complexOfDoubledRealLinearEquiv x) := by
  funext i
  apply Complex.ext <;>
    simp [complexOfDoubledRealLinearEquiv, complexOfDoubledReal,
      complexMatrixRealification, complexMatrixRealPart, complexMatrixImagPart,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib] <;>
    ring

/-- The real algebra norm on `ℂ` is the squared complex norm. -/
theorem complex_algebraNorm_eq_normSq (z : ℂ) :
    Algebra.norm ℝ z = Complex.normSq z := by
  calc
    Algebra.norm ℝ z = (Algebra.leftMulMatrix Complex.basisOneI z).det :=
      Algebra.norm_eq_matrix_det Complex.basisOneI z
    _ = Complex.normSq z := by
      rw [Matrix.det_fin_two]
      simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
        Complex.basisOneI, Complex.normSq_apply]

/-- The determinant of complex realification is the squared norm of the complex determinant. -/
theorem det_complexMatrixRealification (A : Matrix n n ℂ) :
    (complexMatrixRealification A).det = Complex.normSq A.det := by
  let e : (n ⊕ n → ℝ) ≃ₗ[ℝ] (n → ℂ) := complexOfDoubledRealLinearEquiv
  let g : (n ⊕ n → ℝ) →ₗ[ℝ] (n ⊕ n → ℝ) :=
    Matrix.toLin' (complexMatrixRealification A)
  let f : (n → ℂ) →ₗ[ℂ] (n → ℂ) := Matrix.toLin' A
  let fR : (n → ℂ) →ₗ[ℝ] (n → ℂ) := LinearMap.restrictScalars ℝ f
  have hconj : e.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap = fR := by
    apply LinearMap.ext
    intro z
    funext i
    have h := complexOfDoubledRealLinearEquiv_realification_mulVec
      (A := A) (x := e.symm z)
    exact congrFun h i
  calc
    (complexMatrixRealification A).det = LinearMap.det g := by
      simpa [g, ← Matrix.toLin_eq_toLin'] using
        (LinearMap.det_toLin (Pi.basisFun ℝ (n ⊕ n))
          (complexMatrixRealification A)).symm
    _ = LinearMap.det (e.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap) := by
      symm
      exact LinearMap.det_conj g e
    _ = LinearMap.det fR := by rw [hconj]
    _ = Algebra.norm ℝ (LinearMap.det f) := by
      simpa [fR] using
        (LinearMap.det_restrictScalars (R := ℝ) (f := f))
    _ = Algebra.norm ℝ A.det := by
      congr 1
      simpa [f, ← Matrix.toLin_eq_toLin'] using
        LinearMap.det_toLin (Pi.basisFun ℂ n) A
    _ = Complex.normSq A.det := complex_algebraNorm_eq_normSq A.det

omit [Fintype n] in
/-- Doubled-real conjugation is self-adjoint. -/
theorem doubledRealConjugation_conjTranspose :
    (doubledRealConjugation (n := n))ᴴ = doubledRealConjugation := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [doubledRealConjugation, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, eq_comm]

/-- The squared determinant of doubled-real conjugation is one. -/
theorem det_doubledRealConjugation_sq :
    (doubledRealConjugation (n := n)).det ^ (2 : ℕ) = 1 := by
  have hdet : (doubledRealConjugation (n := n)).det =
      (-1 : ℝ) ^ Fintype.card n := by
    change (matrixOrthogonalSum (1 : Matrix n n ℝ) (-1)).det = _
    rw [det_matrixOrthogonalSum]
    simp [Matrix.det_neg]
  rw [hdet]
  rw [← pow_mul]
  simp

/-- Row-convention realification has the same determinant as standard realification. -/
theorem det_complexMatrixRowRealification (A : Matrix n n ℂ) :
    (complexMatrixRowRealification A).det = Complex.normSq A.det := by
  let C := doubledRealConjugation (n := n)
  have hC : C.det ^ (2 : ℕ) = 1 := by
    exact det_doubledRealConjugation_sq (n := n)
  rw [complexMatrixRowRealification, doubledRealConjugation_conjTranspose]
  rw [Matrix.det_mul, Matrix.det_mul, det_complexMatrixRealification]
  change C.det * Complex.normSq A.det * C.det = Complex.normSq A.det
  calc
    C.det * Complex.normSq A.det * C.det =
        Complex.normSq A.det * C.det ^ (2 : ℕ) := by ring
    _ = Complex.normSq A.det := by rw [hC]; ring

end

end GaloisForLFunctions.HTGeometry
