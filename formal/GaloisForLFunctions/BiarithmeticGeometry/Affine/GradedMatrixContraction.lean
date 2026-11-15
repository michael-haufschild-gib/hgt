import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Integer-weighted matrix contraction

Diagonal rescaling assigns the exponent `a i - b j` to a matrix entry.
Intermediate weights cancel under multiplication. Entries supported where
the row weight does not exceed the column weight contract whenever the
absolute scale is at least one. This controls inverses of selected shear
coordinates without estimating a parameter-dependent matrix inverse.
-/

open scoped Matrix BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.GradedMatrix
noncomputable section
variable {ι κ ν : Type*}

/-- Rescale rows and columns by their integer weights. -/
def scale (θ : ℝ) (a : ι → ℤ) (b : κ → ℤ) (M : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  fun i j => θ ^ (a i - b j) * M i j

/-- Matching intermediate weights cancel in a matrix product. -/
theorem scale_mul [Fintype κ] (θ : ℝ) (hθ : θ ≠ 0)
    (a : ι → ℤ) (b : κ → ℤ) (c : ν → ℤ)
    (M : Matrix ι κ ℝ) (N : Matrix κ ν ℝ) :
    scale θ a b M * scale θ b c N = scale θ a c (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hp : θ ^ (a i - b k) * θ ^ (b k - c j) = θ ^ (a i - c j) := by
    rw [← zpow_add₀ hθ]
    congr 1
    omega
  calc
    _ = (θ ^ (a i - b k) * θ ^ (b k - c j)) * (M i k * N k j) := by ring
    _ = _ := by rw [hp]

/-- Equal row and column weights leave the identity matrix unchanged. -/
theorem scale_one [DecidableEq ι] (θ : ℝ) (a : ι → ℤ) :
    scale θ a a (1 : Matrix ι ι ℝ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [scale, Matrix.one_apply, ite_true, sub_self, zpow_zero, one_mul]
  · simp only [scale, Matrix.one_apply, h, ite_false, mul_zero]

/-- Nonpositive entry weights give contraction at every large absolute scale. -/
theorem abs_scale_le (θ : ℝ) (hθ : 1 ≤ |θ|) (a : ι → ℤ) (b : κ → ℤ)
    (M : Matrix ι κ ℝ) (hs : ∀ i j, M i j ≠ 0 → a i ≤ b j) (i : ι) (j : κ) :
    |scale θ a b M i j| ≤ |M i j| := by
  by_cases hm : M i j = 0
  · simp only [scale, hm, mul_zero, abs_zero, le_refl]
  · have hp : |θ ^ (a i - b j)| ≤ 1 := by
      rw [abs_zpow]
      simpa using zpow_le_zpow_right₀ hθ (sub_nonpos.mpr (hs i j hm))
    simpa only [scale, abs_mul, one_mul] using
      mul_le_mul_of_nonneg_right hp (abs_nonneg (M i j))

/-- Rescaling preserves a right-inverse identity when the weights match. -/
theorem scale_right_inverse [Fintype κ] [DecidableEq ι]
    (θ : ℝ) (hθ : θ ≠ 0) (a : ι → ℤ) (b : κ → ℤ)
    (M : Matrix ι κ ℝ) (N : Matrix κ ι ℝ) (hMN : M * N = 1) :
    scale θ a b M * scale θ b a N = 1 := by
  rw [scale_mul θ hθ a b a, hMN, scale_one]

#print axioms scale_mul
#print axioms scale_one
#print axioms abs_scale_le
#print axioms scale_right_inverse

end
end GaloisForLFunctions.BiarithmeticGeometry.GradedMatrix
