import GaloisForLFunctions.HTGeometry.LinearAlgebra.FiniteBilinearCorrection
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Forced quadratic maxima and inverse energies

For a positive definite real matrix `A`, the forced quadratic function
`2 b·x - x·A x` has unique maximum `b·A⁻¹b` at `x = A⁻¹b`.
The gap is exactly the `A`-energy of `x - A⁻¹b`. This gives both a
variational interpretation and a sharp equality criterion for correction heights.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- The quadratic value with linear forcing by the charge vector. -/
def matrixForcedValue (A : Matrix ι ι ℝ) (b x : ι → ℝ) : ℝ :=
  2 * (b ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x)

/-- Inverse precision solves the charge equation. -/
theorem matrix_positive_response (A : Matrix ι ι ℝ) (hA : A.PosDef) (b : ι → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
    Matrix.one_mulVec]

/-- The bilinear form of a positive definite real matrix is symmetric. -/
theorem matrix_positive_form_symm (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (Matrix.toBilin' A).IsSymm := by
  have hAt : A.transpose = A := by
    ext i j
    simpa only [Matrix.transpose_apply, star_trivial] using hA.isHermitian.apply i j
  constructor
  intro x y
  simp only [Matrix.toBilin'_apply']
  rw [dotProduct_mulVec, ← mulVec_transpose, hAt, dotProduct_comm]

/-- The loss from the optimal value is the exact energy of the response error. -/
theorem matrix_forced_value_gap (A : Matrix ι ι ℝ) (hA : A.PosDef) (b x : ι → ℝ) :
    b ⬝ᵥ (A⁻¹ *ᵥ b) - matrixForcedValue A b x =
      (x - A⁻¹ *ᵥ b) ⬝ᵥ (A *ᵥ (x - A⁻¹ *ᵥ b)) := by
  have hB := matrix_positive_form_symm A hA
  have hrep (y : ι → ℝ) : Matrix.toBilin' A (A⁻¹ *ᵥ b) y = b ⬝ᵥ y := by
    rw [hB.eq, Matrix.toBilin'_apply', matrix_positive_response A hA, dotProduct_comm]
  have h := bilinear_square_completion (Matrix.toBilin' A) hB (A⁻¹ *ᵥ b) x
  rw [hrep, hrep, Matrix.toBilin'_apply', Matrix.toBilin'_apply'] at h
  exact h

/-- Inverse energy bounds every forced quadratic value. -/
theorem matrix_forced_value_le (A : Matrix ι ι ℝ) (hA : A.PosDef) (b x : ι → ℝ) :
    matrixForcedValue A b x ≤ b ⬝ᵥ (A⁻¹ *ᵥ b) := by
  have hnon : 0 ≤ (x - A⁻¹ *ᵥ b) ⬝ᵥ (A *ᵥ (x - A⁻¹ *ᵥ b)) := by
    simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg (x - A⁻¹ *ᵥ b)
  rw [← matrix_forced_value_gap A hA b x] at hnon
  exact sub_nonneg.mp hnon

/-- The inverse response is the unique maximizer. -/
theorem matrix_forced_value_eq_iff (A : Matrix ι ι ℝ) (hA : A.PosDef) (b x : ι → ℝ) :
    matrixForcedValue A b x = b ⬝ᵥ (A⁻¹ *ᵥ b) ↔ x = A⁻¹ *ᵥ b := by
  constructor
  · intro hx
    by_contra hne
    have hpos := hA.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    simp only [star_trivial] at hpos
    rw [← matrix_forced_value_gap A hA b x, hx, sub_self] at hpos
    exact (lt_irrefl 0) hpos
  · rintro rfl
    have h := matrix_forced_value_gap A hA b (A⁻¹ *ᵥ b)
    rw [sub_self, Matrix.mulVec_zero, dotProduct_zero] at h
    exact (sub_eq_zero.mp h).symm

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.matrix_forced_value_gap
#print axioms GaloisForLFunctions.HTGeometry.matrix_forced_value_eq_iff
