import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Multiplying a module-valued matrix by scalar matrices

The matrix levels of an operator system are the spaces `Mₙ(V)` for a `*`-vector space `V`, and the
compatibility axiom of a matrix ordering is stability under the compression `x ↦ α* x α` by scalar
rectangular matrices.  The underlying operation — matrix multiplication with one factor valued in a
module and the other in the scalars — is developed here: `mulLeft`, `mulRight`, their unit and
associativity laws, the commutation of the two sides, and the compression itself together with its
composition law

```text
compress (α * β) x = compress β (compress α x),
```

which is what makes a compression-stable family of cones stable under composing compressions.
-/

namespace GaloisForLFunctions.HTGeometry

namespace MatrixModule

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {l m n p : Type*}

/-- Multiply a module-valued matrix on the left by a scalar matrix. -/
def mulLeft [Fintype m] (A : Matrix l m 𝕜) (B : Matrix m n V) : Matrix l n V :=
  Matrix.of fun i j => ∑ k, A i k • B k j

/-- Multiply a module-valued matrix on the right by a scalar matrix. -/
def mulRight [Fintype m] (B : Matrix l m V) (A : Matrix m n 𝕜) : Matrix l n V :=
  Matrix.of fun i j => ∑ k, A k j • B i k

@[simp]
theorem mulLeft_apply [Fintype m] (A : Matrix l m 𝕜) (B : Matrix m n V) (i : l) (j : n) :
    mulLeft A B i j = ∑ k, A i k • B k j := rfl

@[simp]
theorem mulRight_apply [Fintype m] (B : Matrix l m V) (A : Matrix m n 𝕜) (i : l) (j : n) :
    mulRight B A i j = ∑ k, A k j • B i k := rfl

@[simp]
theorem mulLeft_one [Fintype m] [DecidableEq m] (B : Matrix m n V) :
    mulLeft (1 : Matrix m m 𝕜) B = B := by
  ext i j
  simp [mulLeft, Matrix.one_apply]

@[simp]
theorem mulRight_one [Fintype m] [DecidableEq m] (B : Matrix l m V) :
    mulRight B (1 : Matrix m m 𝕜) = B := by
  ext i j
  simp [mulRight, Matrix.one_apply]

theorem mulLeft_assoc [Fintype m] [Fintype n] (A : Matrix l m 𝕜) (A' : Matrix m n 𝕜)
    (B : Matrix n p V) : mulLeft A (mulLeft A' B) = mulLeft (A * A') B := by
  ext i j
  simp only [mulLeft_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem mulRight_assoc [Fintype m] [Fintype n] (B : Matrix l m V) (A : Matrix m n 𝕜)
    (A' : Matrix n p 𝕜) : mulRight (mulRight B A) A' = mulRight B (A * A') := by
  ext i j
  simp only [mulRight_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-- Left and right multiplication by scalar matrices commute. -/
theorem mulRight_mulLeft [Fintype m] [Fintype n] (A : Matrix l m 𝕜) (B : Matrix m n V)
    (A' : Matrix n p 𝕜) : mulRight (mulLeft A B) A' = mulLeft A (mulRight B A') := by
  ext i j
  simp only [mulRight_apply, mulLeft_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-! ### Additivity -/

theorem mulLeft_add [Fintype m] (A : Matrix l m 𝕜) (B B' : Matrix m n V) :
    mulLeft A (B + B') = mulLeft A B + mulLeft A B' := by
  ext i j
  simp [mulLeft, Finset.sum_add_distrib]

theorem add_mulLeft [Fintype m] (A A' : Matrix l m 𝕜) (B : Matrix m n V) :
    mulLeft (A + A') B = mulLeft A B + mulLeft A' B := by
  ext i j
  simp [mulLeft, add_smul, Finset.sum_add_distrib]

theorem mulRight_add [Fintype m] (B B' : Matrix l m V) (A : Matrix m n 𝕜) :
    mulRight (B + B') A = mulRight B A + mulRight B' A := by
  ext i j
  simp [mulRight, Finset.sum_add_distrib]

theorem mulRight_add_right [Fintype m] (B : Matrix l m V) (A A' : Matrix m n 𝕜) :
    mulRight B (A + A') = mulRight B A + mulRight B A' := by
  ext i j
  simp [mulRight, add_smul, Finset.sum_add_distrib]

@[simp]
theorem mulLeft_zero [Fintype m] (A : Matrix l m 𝕜) :
    mulLeft A (0 : Matrix m n V) = 0 := by
  ext i j; simp [mulLeft]

@[simp]
theorem zero_mulLeft [Fintype m] (B : Matrix m n V) :
    mulLeft (0 : Matrix l m 𝕜) B = 0 := by
  ext i j; simp [mulLeft]

@[simp]
theorem mulRight_zero [Fintype m] (B : Matrix l m V) :
    mulRight B (0 : Matrix m n 𝕜) = 0 := by
  ext i j; simp [mulRight]

@[simp]
theorem zero_mulRight [Fintype m] (A : Matrix m n 𝕜) :
    mulRight (0 : Matrix l m V) A = 0 := by
  ext i j; simp [mulRight]

theorem mulLeft_smul [Fintype m] (c : 𝕜) (A : Matrix l m 𝕜) (B : Matrix m n V) :
    mulLeft A (c • B) = c • mulLeft A B := by
  ext i j
  simp only [mulLeft_apply, Matrix.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

theorem mulRight_smul [Fintype m] (c : 𝕜) (B : Matrix l m V) (A : Matrix m n 𝕜) :
    mulRight (c • B) A = c • mulRight B A := by
  ext i j
  simp only [mulRight_apply, Matrix.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

/-! ## Compression -/

variable [StarRing 𝕜]

/-- Compression of a module-valued square matrix by a scalar rectangular matrix. -/
def compress [Fintype m] (α : Matrix m n 𝕜) (x : Matrix m m V) : Matrix n n V :=
  mulRight (mulLeft αᴴ x) α

theorem compress_apply [Fintype m] (α : Matrix m n 𝕜) (x : Matrix m m V) (i j : n) :
    compress α x i j = ∑ b, α b j • ∑ a, star (α a i) • x a b := rfl

@[simp]
theorem compress_one [Fintype m] [DecidableEq m] (x : Matrix m m V) :
    compress (1 : Matrix m m 𝕜) x = x := by
  rw [compress, Matrix.conjTranspose_one, mulLeft_one, mulRight_one]

@[simp]
theorem compress_zero [Fintype m] (α : Matrix m n 𝕜) :
    compress α (0 : Matrix m m V) = 0 := by
  rw [compress, mulLeft_zero, zero_mulRight]

@[simp]
theorem zero_compress [Fintype m] (x : Matrix m m V) :
    compress (0 : Matrix m n 𝕜) x = 0 := by
  rw [compress, Matrix.conjTranspose_zero, zero_mulLeft, zero_mulRight]

theorem compress_add [Fintype m] (α : Matrix m n 𝕜) (x y : Matrix m m V) :
    compress α (x + y) = compress α x + compress α y := by
  rw [compress, compress, compress, mulLeft_add, mulRight_add]

theorem compress_smul [Fintype m] (c : 𝕜) (α : Matrix m n 𝕜) (x : Matrix m m V) :
    compress α (c • x) = c • compress α x := by
  rw [compress, compress, mulLeft_smul, mulRight_smul]

/-- **Compressions compose.**  Compressing by a product is compressing twice, so a family of cones
stable under all compressions is automatically stable under composing them. -/
theorem compress_mul [Fintype m] [Fintype n] (α : Matrix m n 𝕜) (β : Matrix n p 𝕜)
    (x : Matrix m m V) : compress (α * β) x = compress β (compress α x) := by
  simp only [compress, Matrix.conjTranspose_mul, ← mulLeft_assoc, mulRight_mulLeft,
    mulRight_assoc]

/-- Compressing by a matrix split into two column blocks produces the corresponding `2 × 2` block
matrix, whose diagonal blocks are the two individual compressions. -/
theorem compress_fromCols [Fintype m] {n₁ n₂ : Type*} (α : Matrix m n₁ 𝕜) (β : Matrix m n₂ 𝕜)
    (x : Matrix m m V) :
    compress (Matrix.fromCols α β) x
      = Matrix.fromBlocks (compress α x) (mulRight (mulLeft αᴴ x) β)
          (mulRight (mulLeft βᴴ x) α) (compress β x) := by
  ext i j
  cases i <;> cases j <;>
    simp [compress, mulLeft, mulRight, Matrix.fromCols]

end MatrixModule

end GaloisForLFunctions.HTGeometry
