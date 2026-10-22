import Mathlib.Analysis.Matrix.PosDef

/-!
# Moving-minimizer reserve in a center-integrated Schur source

The inverse of an integrated head is fixed across centers. The inverse of a
positive local head moves with the center. Completing the square exposes the
nonnegative variance omitted by pointwise Schur-complement arguments.
-/

namespace RHTower
noncomputable section
open Matrix

/-- Exact completion of the square for a fixed vector and a local normal-equation solution. -/
theorem schurMovingMinimizer_algebra {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (b u w : n → ℝ)
    (hA : Aᵀ = A) (hu : A *ᵥ u = b) :
    w ⬝ᵥ (A *ᵥ w) - 2 * (w ⬝ᵥ b) + u ⬝ᵥ b =
      (w-u) ⬝ᵥ (A *ᵥ (w-u)) := by
  have hsym : u ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ u) := by
    calc
      _ = u ⬝ᵥ (Aᵀ *ᵥ w) := by rw [hA]
      _ = _ := dotProduct_transpose_mulVec A u w
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  rw [hsym, hu]
  ring

/-- A positive local head makes the moving-minimizer discrepancy nonnegative. -/
theorem schurMovingMinimizer_nonneg {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (b u w : n → ℝ)
    (hA : A.PosDef) (hu : A *ᵥ u = b) :
    0 ≤ w ⬝ᵥ (A *ᵥ w) - 2 * (w ⬝ᵥ b) + u ⬝ᵥ b := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  rw [schurMovingMinimizer_algebra A b u w hs hu]
  simpa using hA.posSemidef.dotProduct_mulVec_nonneg (w-u)

/-- The inverse-local-head formula retains the exact positive-square reserve. -/
theorem schurMovingMinimizer_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b w : n → ℝ) (hA : A.PosDef) :
    w ⬝ᵥ (A *ᵥ w) - 2 * (w ⬝ᵥ b) + (A⁻¹ *ᵥ b) ⬝ᵥ b =
      (w-A⁻¹ *ᵥ b) ⬝ᵥ (A *ᵥ (w-A⁻¹ *ᵥ b)) := by
  have hdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA.isUnit
  have hu : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  exact schurMovingMinimizer_algebra A b (A⁻¹ *ᵥ b) w hs hu

end
end RHTower
