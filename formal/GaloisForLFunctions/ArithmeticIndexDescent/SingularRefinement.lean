import GaloisForLFunctions.HTGeometry.HaynsworthInertia

/-!
# Refinement with a singular corner

When the mixed block factors as `A * X`, triangular congruence removes it without
inverting `A`. The three inertia indices split between `A` and `C - Xᴴ * A * X`.
This complement is independent of the chosen factorization. Thus a presentation
may retain its relations; invertibility is not part of the descent operation.

The factorization is the exact range-compatibility condition. Establishing it and
estimating the resulting complement remain necessary for a specified arithmetic form.
-/

open Matrix

namespace GaloisForLFunctions.ArithmeticIndexDescent

open HTGeometry

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A mixed block in the range of the old corner admits elimination even when that corner is singular. -/
theorem singular_schur_congruence {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X : Matrix ι κ ℂ) (C : Matrix κ κ ℂ) :
    (fromBlocks 1 X 0 1)ᴴ * fromBlocks A 0 0 (C - Xᴴ * A * X) *
        fromBlocks 1 X 0 1 = fromBlocks A (A * X) (A * X)ᴴ C := by
  rw [Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.conjTranspose_mul, hA.eq]
  congr 1
  abel

/-- The singular Schur complement is Hermitian. -/
theorem isHermitian_singular_schur {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X : Matrix ι κ ℂ) {C : Matrix κ κ ℂ} (hC : C.IsHermitian) :
    (C - Xᴴ * A * X).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hC.eq,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/-- Different lifts of one mixed block produce the same complement. -/
theorem singular_schur_independent_of_lift {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {X Y : Matrix ι κ ℂ} (hXY : A * X = A * Y) (C : Matrix κ κ ℂ) :
    C - Xᴴ * A * X = C - Yᴴ * A * Y := by
  have hstar : Xᴴ * A = Yᴴ * A := by
    simpa only [Matrix.conjTranspose_mul, hA.eq] using
      congrArg Matrix.conjTranspose hXY
  rw [hstar, Matrix.mul_assoc, hXY, ← Matrix.mul_assoc]

/-- Negative squares split exactly under a range-compatible refinement. -/
theorem negIndex_singular_refinement {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X : Matrix ι κ ℂ) {C : Matrix κ κ ℂ} (hC : C.IsHermitian) :
    hermNegIndex (fromBlocks A (A * X) (A * X)ᴴ C) =
      hermNegIndex A + hermNegIndex (C - Xᴴ * A * X) := by
  rw [← singular_schur_congruence hA X C,
    negIndex_conjugate _ (isUnit_fromBlocks_one_upper X),
    negIndex_fromBlocks_zero hA (isHermitian_singular_schur hA X hC)]

/-- Positive squares satisfy the same singular refinement law. -/
theorem posIndex_singular_refinement {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X : Matrix ι κ ℂ) {C : Matrix κ κ ℂ} (hC : C.IsHermitian) :
    hermPosIndex (fromBlocks A (A * X) (A * X)ᴴ C) =
      hermPosIndex A + hermPosIndex (C - Xᴴ * A * X) := by
  rw [← singular_schur_congruence hA X C,
    posIndex_conjugate _ (isUnit_fromBlocks_one_upper X),
    posIndex_fromBlocks_zero hA (isHermitian_singular_schur hA X hC)]

/-- Presentation relations are retained by the null-index refinement law. -/
theorem nullIndex_singular_refinement {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X : Matrix ι κ ℂ) {C : Matrix κ κ ℂ} (hC : C.IsHermitian) :
    hermNullIndex (fromBlocks A (A * X) (A * X)ᴴ C) =
      hermNullIndex A + hermNullIndex (C - Xᴴ * A * X) := by
  rw [← singular_schur_congruence hA X C,
    nullIndex_conjugate _ (isUnit_fromBlocks_one_upper X),
    nullIndex_fromBlocks_zero hA (isHermitian_singular_schur hA X hC)]

end GaloisForLFunctions.ArithmeticIndexDescent
