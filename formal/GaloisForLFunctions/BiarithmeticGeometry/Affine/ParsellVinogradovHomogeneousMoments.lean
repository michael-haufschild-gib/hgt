import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearMinors
import Mathlib.LinearAlgebra.Determinant

/-!
# Homogeneous moment coordinates for the binomial shear

The degree-`d` moment vector is `(x^d, x^(d-1)z, …, z^d)`.
The binomial shear matrix sends this vector to the moment vector at
`(x,z+θx)`. Thus the matrix overlap estimates apply to the actual homogeneous
blocks of the polynomial moment map.
-/

open scoped Matrix BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The homogeneous degree-`d` monomials ordered by increasing vertical exponent. -/
def homogeneousMoment (d : ℕ) (x z : ℝ) : Fin (d + 1) → ℝ :=
  fun i => x ^ (d - i.val) * z ^ i.val

/-- Binomial shear acts on the genuine homogeneous moment coordinates. -/
theorem shearBlock_mul_homogeneousMoment (d : ℕ) (θ x z : ℝ) :
    shearBlock (d + 1) θ *ᵥ homogeneousMoment d x z =
      homogeneousMoment d x (z + θ * x) := by
  funext i
  change (∑ j : Fin (d + 1),
    (Nat.choose i.val j.val : ℝ) * θ ^ (i.val - j.val) *
      (x ^ (d - j.val) * z ^ j.val)) = x ^ (d - i.val) * (z + θ * x) ^ i.val
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (Nat.choose i.val j : ℝ) * θ ^ (i.val - j) * (x ^ (d - j) * z ^ j)) (d + 1)]
  have htruncate :
      (∑ j ∈ Finset.range (i.val + 1), (Nat.choose i.val j : ℝ) * θ ^ (i.val - j) *
        (x ^ (d - j) * z ^ j)) =
      ∑ j ∈ Finset.range (d + 1), (Nat.choose i.val j : ℝ) * θ ^ (i.val - j) *
        (x ^ (d - j) * z ^ j) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hji : i.val < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    rw [Nat.choose_eq_zero_of_lt hji, Nat.cast_zero, zero_mul, zero_mul]
  rw [← htruncate, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i.val := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hp : x ^ (d - i.val) * x ^ (i.val - j) = x ^ (d - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow]
  calc
    _ = (Nat.choose i.val j : ℝ) * θ ^ (i.val - j) *
        ((x ^ (d - i.val) * x ^ (i.val - j)) * z ^ j) := by rw [hp]
    _ = _ := by ring

/-- The corresponding linear map realizes the same shear on homogeneous moments. -/
theorem shearLinear_homogeneousMoment (d : ℕ) (θ x z : ℝ) :
    Matrix.toLin' (shearBlock (d + 1) θ) (homogeneousMoment d x z) =
      homogeneousMoment d x (z + θ * x) := by
  rw [Matrix.toLin'_apply, shearBlock_mul_homogeneousMoment]

#print axioms shearBlock_mul_homogeneousMoment
#print axioms shearLinear_homogeneousMoment

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
