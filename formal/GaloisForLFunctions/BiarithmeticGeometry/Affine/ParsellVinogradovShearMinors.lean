import GaloisForLFunctions.HTGeometry.BinomialNodeDeterminant
import Mathlib.Data.Real.Basic

/-!
# Exact powers in binomial shear minors

In a shear block of size `2q+r`, take the last `q` rows and first `q`
columns. Row and column powers factor its determinant as a nonzero binomial
constant times `θ^(q(q+r))`. For balanced blocks (`r=0` or `r=1`), this
exponent is the integral part of one quarter of the squared block size.
-/

set_option autoImplicit false

open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The binomial shear matrix on a homogeneous block of dimension `m`. -/
def shearBlock (m : ℕ) (θ : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (Nat.choose i.val j.val : ℝ) * θ ^ (i.val - j.val)

/-- The binomial shear is triangular with unit diagonal, hence has determinant one. -/
theorem det_shearBlock (m : ℕ) (θ : ℝ) : (shearBlock m θ).det = 1 := by
  have ht : (shearBlock m θ).transpose.BlockTriangular id := by
    intro i j hji
    have h : j.val < i.val := hji
    change (Nat.choose j.val i.val : ℝ) * θ ^ (j.val - i.val) = 0
    rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul]
  rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular ht]
  simp [shearBlock]

/-- The final `q` rows in a block of size `2q+r`. -/
def shearMinorRows (q r : ℕ) : Fin q ↪ Fin (2 * q + r) where
  toFun i := ⟨q + r + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv : q + r + i.val = q + r + j.val := congrArg (fun z : Fin (2 * q + r) => z.val) h
    exact Nat.add_left_cancel hv

/-- The first `q` columns in the same block. -/
def shearMinorCols (q r : ℕ) : Fin q ↪ Fin (2 * q + r) where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun z : Fin (2 * q + r) => z.val) h

/-- The last-row, first-column minor of a homogeneous binomial shear block. -/
def shearMinor (q r : ℕ) (θ : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (Nat.choose (q + r + i.val) j.val : ℝ) * θ ^ (q + r + i.val - j.val)

/-- The selected binomial matrix is a literal minor of the full shear block. -/
theorem shearMinor_eq_submatrix (q r : ℕ) (θ : ℝ) :
    shearMinor q r θ = (shearBlock (2 * q + r) θ).submatrix
      (shearMinorRows q r) (shearMinorCols q r) := rfl

/-- Its coefficient at the exact shear power. -/
def shearMinorConstant (q r : ℕ) : ℝ :=
  (binomNodeMatrix ℝ (fun i : Fin q => q + r + i.val)).det

/-- Distinct consecutive binomial nodes make the shear coefficient nonzero. -/
theorem shearMinorConstant_ne_zero (q r : ℕ) : shearMinorConstant q r ≠ 0 := by
  apply det_binomNodeMatrix_ne_zero
  intro i j h
  apply Fin.ext
  exact Nat.add_left_cancel h

private theorem shearMinor_factor (q r : ℕ) (θ : ℝ) :
    shearMinor q r θ =
      (Matrix.diagonal (fun i : Fin q => θ ^ i.val) *
        binomNodeMatrix ℝ (fun i : Fin q => q + r + i.val)) *
          Matrix.diagonal (fun j : Fin q => θ ^ (q + r - j.val)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have he : q + r + i.val - j.val = i.val + (q + r - j.val) := by omega
  simp only [shearMinor, binomNodeMatrix, Matrix.of_apply, he, pow_add]
  ring

private theorem shearMinor_power_product (q r : ℕ) (θ : ℝ) :
    (∏ i : Fin q, θ ^ i.val) * (∏ i : Fin q, θ ^ (q + r - i.val)) = θ ^ (q * (q + r)) := by
  calc
    _ = ∏ i : Fin q, θ ^ i.val * θ ^ (q + r - i.val) := Finset.prod_mul_distrib.symm
    _ = ∏ _i : Fin q, θ ^ (q + r) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_add, show i.val + (q + r - i.val) = q + r by omega]
    _ = (θ ^ (q + r)) ^ q := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = θ ^ (q * (q + r)) := by rw [← pow_mul, Nat.mul_comm (q + r) q]

/-- The determinant has one exact shear power, including at zero shear. -/
theorem det_shearMinor (q r : ℕ) (θ : ℝ) :
    (shearMinor q r θ).det = shearMinorConstant q r * θ ^ (q * (q + r)) := by
  rw [shearMinor_factor, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal]
  calc
    _ = shearMinorConstant q r *
        ((∏ i : Fin q, θ ^ i.val) * (∏ i : Fin q, θ ^ (q + r - i.val))) := by
      rw [mul_assoc, mul_left_comm]
      rfl
    _ = _ := congrArg (fun z : ℝ => shearMinorConstant q r * z) (shearMinor_power_product q r θ)

/-- The selected minor is nonsingular exactly away from zero shear, unless it is empty. -/
theorem det_shearMinor_ne_zero_iff (q r : ℕ) (θ : ℝ) :
    (shearMinor q r θ).det ≠ 0 ↔ q = 0 ∨ θ ≠ 0 := by
  rw [det_shearMinor]
  constructor
  · intro h
    by_cases hq : q = 0
    · exact Or.inl hq
    · right
      intro hθ
      apply h
      rw [hθ, zero_pow (Nat.mul_ne_zero hq (by omega)), mul_zero]
  · rintro (hq | hθ)
    · subst q
      simpa only [Nat.zero_mul, pow_zero, mul_one] using shearMinorConstant_ne_zero 0 r
    · exact mul_ne_zero (shearMinorConstant_ne_zero q r) (pow_ne_zero _ hθ)

/-- Balanced even blocks attain the integral quarter-square exponent. -/
theorem det_shearMinor_even (q : ℕ) (θ : ℝ) :
    (shearMinor q 0 θ).det = shearMinorConstant q 0 * θ ^ ((2 * q) ^ 2 / 4) := by
  rw [det_shearMinor]
  have he : (2 * q) ^ 2 = 4 * (q * (q + 0)) := by ring
  rw [he]
  congr 2
  omega

/-- Balanced odd blocks attain the same integral quarter-square law. -/
theorem det_shearMinor_odd (q : ℕ) (θ : ℝ) :
    (shearMinor q 1 θ).det = shearMinorConstant q 1 * θ ^ ((2 * q + 1) ^ 2 / 4) := by
  rw [det_shearMinor]
  have he : (2 * q + 1) ^ 2 = 4 * (q * (q + 1)) + 1 := by ring
  rw [he]
  congr 2
  omega

#print axioms det_shearBlock
#print axioms shearMinor_eq_submatrix
#print axioms shearMinorConstant_ne_zero
#print axioms det_shearMinor
#print axioms det_shearMinor_ne_zero_iff
#print axioms det_shearMinor_even
#print axioms det_shearMinor_odd

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
