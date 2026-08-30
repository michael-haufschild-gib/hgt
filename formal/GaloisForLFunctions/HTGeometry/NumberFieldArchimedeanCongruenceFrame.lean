import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanMinorLogSum
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiActionReduction

/-!
# Number-field congruence frames at real and complex places

The leading block of a Hermitian congruence is the Gram form on its leading-column frame.  For the
number-field action that frame is formed from rows of the original integral matrix.  At a complex
place its selected determinant is the conjugate of the embedding of the same integral row minor;
at a real place it is the corresponding real embedding.  Hence both local types use one global
minor and its actual infinite-place absolute value.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n k : ℕ}

/-- The leading block of a complex Hermitian congruence is the congruence by the leading columns. -/
theorem complexLeadingBlock_congr_frame (hk : k ≤ n)
    (M γ : Matrix (Fin n) (Fin n) ℂ) :
    complexLeadingBlock hk (Matrix.conjTranspose γ * M * γ) =
      Matrix.conjTranspose (γ.submatrix id (Fin.castLE hk)) * M *
        (γ.submatrix id (Fin.castLE hk)) := by
  ext a b
  show (Matrix.conjTranspose γ * M * γ) (Fin.castLE hk a) (Fin.castLE hk b) = _
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1

omit [NumberField K] in
/-- A selected complex action-frame determinant is the conjugate of the same embedded integral
row minor. -/
theorem numberFieldComplex_conjTransposeFrame_minor_det
    (w : {w : InfinitePlace K // w.IsComplex})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) (hk : k ≤ n)
    (rows : Fin k → Fin n) :
    ((Matrix.submatrix (Matrix.conjTranspose (numberFieldComplexOrderMatrixAt w M))
      id (Fin.castLE hk)).submatrix rows id).det =
      star ((numberFieldComplexOrderMatrixAt w
        ((Matrix.transpose M).submatrix rows (Fin.castLE hk))).det) := by
  let Q : Matrix (Fin k) (Fin k) ℂ :=
    numberFieldComplexOrderMatrixAt w
      ((Matrix.transpose M).submatrix rows (Fin.castLE hk))
  have hmatrix :
      (Matrix.submatrix (Matrix.conjTranspose (numberFieldComplexOrderMatrixAt w M))
        id (Fin.castLE hk)).submatrix rows id =
        Matrix.conjTranspose (Matrix.transpose Q) := by
    ext a b
    rfl
  rw [hmatrix, Matrix.det_conjTranspose, Matrix.det_transpose]

omit [NumberField K] in
/-- The norm of a selected complex action-frame determinant is the corresponding infinite-place
absolute value of the global integral row minor. -/
theorem norm_numberFieldComplex_conjTransposeFrame_minor_det
    (w : {w : InfinitePlace K // w.IsComplex})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) (hk : k ≤ n)
    (rows : Fin k → Fin n) :
    ‖((Matrix.submatrix (Matrix.conjTranspose (numberFieldComplexOrderMatrixAt w M))
      id (Fin.castLE hk)).submatrix rows id).det‖ =
      w.1 (((((Matrix.transpose M).submatrix rows
        (Fin.castLE hk)).det : 𝓞 K) : K)) := by
  rw [numberFieldComplex_conjTransposeFrame_minor_det]
  rw [norm_star]
  rw [numberFieldComplexOrderMatrixAt_det]
  change ‖w.1.embedding (((((Matrix.transpose M).submatrix rows
    (Fin.castLE hk)).det : 𝓞 K) : K))‖ = _
  exact w.1.norm_embedding_eq _

omit [NumberField K] in
/-- The absolute value of a selected real action-frame determinant is the corresponding
infinite-place absolute value of the same global integral row minor. -/
theorem abs_numberFieldReal_transposeFrame_minor_det
    (w : {w : InfinitePlace K // w.IsReal})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) (hk : k ≤ n)
    (rows : Fin k → Fin n) :
    |((Matrix.submatrix (Matrix.transpose (numberFieldRealOrderMatrixAt w M))
      id (Fin.castLE hk)).submatrix rows id).det| =
      w.1 (((((Matrix.transpose M).submatrix rows
        (Fin.castLE hk)).det : 𝓞 K) : K)) := by
  have hmatrix :
      (Matrix.submatrix (Matrix.transpose (numberFieldRealOrderMatrixAt w M))
        id (Fin.castLE hk)).submatrix rows id =
        numberFieldRealOrderMatrixAt w
          ((Matrix.transpose M).submatrix rows (Fin.castLE hk)) := by
    ext a b
    rfl
  rw [hmatrix, numberFieldRealOrderMatrixAt_det]
  rw [← w.1.norm_embedding_eq]
  rw [← w.1.embedding_of_isReal_apply w.2]
  exact (Complex.norm_real _).symm

end

end GaloisForLFunctions.HTGeometry
