import GaloisForLFunctions.HTGeometry.OrderPrincipalRestriction

/-!
# Positive-definite real Schur complements

The upper-unitriangular elimination of a real symmetric positive-definite block matrix is carried
out explicitly.  Its trailing Schur complement is therefore positive definite.  This finite-matrix
lemma supplies the positivity step in rank descent for balanced order forms.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem isUnit_fromBlocks_one_upper_real (X : Matrix ι κ ℝ) :
    IsUnit (fromBlocks (1 : Matrix ι ι ℝ) X 0 (1 : Matrix κ κ ℝ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Explicit upper-unitriangular elimination of the cross block. -/
theorem fromBlocks_schur_eliminate_real {A : Matrix ι ι ℝ}
    (hAu : IsUnit A) (hA : Aᵀ = A) (B : Matrix ι κ ℝ) (C : Matrix κ κ ℝ) :
    let X := A⁻¹ * B
    let Q := fromBlocks (1 : Matrix ι ι ℝ) (-X) 0 (1 : Matrix κ κ ℝ)
    Qᵀ * fromBlocks A B Bᵀ C * Q =
      fromBlocks A 0 0 (C - Bᵀ * A⁻¹ * B) := by
  dsimp only
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have htrans : (A⁻¹ * B)ᵀ = Bᵀ * A⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA]
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_neg, htrans]
  simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hAB : A * -(A⁻¹ * B) + B = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hAinv, Matrix.one_mul]
    abel
  have hBA : -(Bᵀ * A⁻¹) * A + Bᵀ = 0 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hinvA, Matrix.mul_one]
    abel
  rw [hAB, hBA, Matrix.zero_mul, zero_add]
  congr 1
  rw [Matrix.neg_mul]
  abel

/-- The Schur complement of a symmetric invertible head in a positive-definite real block matrix
is positive definite. -/
theorem schurComplement_posDef_real {A : Matrix ι ι ℝ} (hAu : IsUnit A)
    (hA : Aᵀ = A) (B : Matrix ι κ ℝ) (C : Matrix κ κ ℝ)
    (hfull : (fromBlocks A B Bᵀ C).PosDef) :
    (C - Bᵀ * A⁻¹ * B).PosDef := by
  let Q := fromBlocks (1 : Matrix ι ι ℝ) (-(A⁻¹ * B)) 0 (1 : Matrix κ κ ℝ)
  have hQ : IsUnit Q := isUnit_fromBlocks_one_upper_real (-(A⁻¹ * B))
  have hQinj : Function.Injective Q.mulVec := Matrix.mulVec_injective_of_isUnit hQ
  have hcongr : (Qᵀ * fromBlocks A B Bᵀ C * Q).PosDef := by
    have hcast : Qᴴ * fromBlocks A B Bᵀ C * Q = Qᵀ * fromBlocks A B Bᵀ C * Q := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [← hcast]
    exact hfull.conjTranspose_mul_mul_same hQinj
  rw [fromBlocks_schur_eliminate_real hAu hA B C] at hcongr
  have hsub := hcongr.submatrix
    (Sum.inr_injective : Function.Injective (Sum.inr : κ → ι ⊕ κ))
  have heq : (fromBlocks A 0 0 (C - Bᵀ * A⁻¹ * B)).submatrix Sum.inr Sum.inr =
      C - Bᵀ * A⁻¹ * B := by
    ext i j
    rfl
  rw [heq] at hsub
  exact hsub

end GaloisForLFunctions.HTGeometry
