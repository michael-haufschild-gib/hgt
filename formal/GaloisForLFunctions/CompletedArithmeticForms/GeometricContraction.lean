import GaloisForLFunctions.HTGeometry.SeparatedOffDiagonalBound
import GaloisForLFunctions.HTGeometry.VerticalKernelDyadicSplit

/-!
# Finite Gaussian contraction majorants

The common contraction degree produces the Gram of a lower triangular geometric
kernel. Its row sums and complete quadratic form have a bound independent of
dimension, with the exact geometric payment `(1-r)⁻²`.
-/

noncomputable section

open Finset Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Lower triangular causal geometric kernel. -/
def geometricLower (N : ℕ) (ρ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j.val ≤ i.val then ρ ^ (i.val - j.val) else 0

/-- Complete common-index contraction kernel. -/
def geometricContraction (N : ℕ) (ρ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  geometricLower N ρ * (geometricLower N ρ).transpose

theorem geometricLower_nonneg {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (i j : Fin N) :
    0 ≤ geometricLower N ρ i j := by
  unfold geometricLower
  split_ifs <;> positivity

/-- Exact row mass before its geometric bound. -/
theorem geometricLower_row_sum (N : ℕ) (ρ : ℝ) (i : Fin N) :
    ∑ j, geometricLower N ρ i j = ∑ j ∈ range (i.val + 1), ρ ^ j := by
  change (∑ j : Fin N, if j.val ≤ i.val then ρ ^ (i.val - j.val) else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ i.val then ρ ^ (i.val - j) else 0) N]
  have hcut : (∑ j ∈ range N, if j ≤ i.val then ρ ^ (i.val - j) else 0) =
      ∑ j ∈ range (i.val + 1), if j ≤ i.val then ρ ^ (i.val - j) else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : i.val + 1 ≤ N))
    intro j hj hj'
    have hjgt : i.val < j := by
      have := Finset.mem_range.not.mp hj'
      omega
    simp only [if_neg (by omega : ¬j ≤ i.val)]
  rw [hcut]
  calc
    _ = ∑ j ∈ range (i.val + 1), ρ ^ (i.val - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
    _ = _ := by
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun j => ρ ^ j) (i.val + 1))

/-- Exact column mass, retaining its finite terminal boundary. -/
theorem geometricLower_column_sum (N : ℕ) (ρ : ℝ) (j : Fin N) :
    ∑ i, geometricLower N ρ i j = ∑ k ∈ range (N - j.val), ρ ^ k := by
  change (∑ i : Fin N, if j.val ≤ i.val then ρ ^ (i.val - j.val) else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if j.val ≤ i then ρ ^ (i - j.val) else 0) N]
  calc
    _ = ∑ i ∈ range (j.val + (N - j.val)),
        if j.val ≤ i then ρ ^ (i - j.val) else 0 := by
      rw [show j.val + (N - j.val) = N by omega]
    _ = _ := by
      rw [Finset.sum_range_add]
      have hz : (∑ i ∈ range j.val, if j.val ≤ i then ρ ^ (i - j.val) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
      rw [hz, zero_add]
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem geometricLower_row_le {N : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (i : Fin N) : ∑ j, geometricLower N ρ i j ≤ (1 - ρ)⁻¹ := by
  rw [geometricLower_row_sum]
  exact GaloisForLFunctions.HTGeometry.sum_range_geom_le_inv hρ0 hρ1 _

theorem geometricLower_column_le {N : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (j : Fin N) : ∑ i, geometricLower N ρ i j ≤ (1 - ρ)⁻¹ := by
  rw [geometricLower_column_sum]
  exact GaloisForLFunctions.HTGeometry.sum_range_geom_le_inv hρ0 hρ1 _

theorem geometricContraction_symm (N : ℕ) (ρ : ℝ) (i j : Fin N) :
    geometricContraction N ρ i j = geometricContraction N ρ j i := by
  simp only [geometricContraction, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem geometricContraction_nonneg {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (i j : Fin N) :
    0 ≤ geometricContraction N ρ i j := by
  simp only [geometricContraction, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (geometricLower_nonneg hρ i k) (geometricLower_nonneg hρ j k)

/-- Exact common contraction sum; no diagonal or boundary term is discarded. -/
theorem geometricContraction_eq_sum (N : ℕ) (ρ : ℝ) (i j : Fin N) :
    geometricContraction N ρ i j =
      ∑ r ∈ range (min i.val j.val + 1), ρ ^ ((i.val - r) + (j.val - r)) := by
  simp only [geometricContraction, Matrix.mul_apply, Matrix.transpose_apply, geometricLower]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    (if r ≤ i.val then ρ ^ (i.val - r) else 0) *
      (if r ≤ j.val then ρ ^ (j.val - r) else 0)) N]
  have hcut : (∑ r ∈ range N,
      (if r ≤ i.val then ρ ^ (i.val - r) else 0) *
        (if r ≤ j.val then ρ ^ (j.val - r) else 0)) =
      ∑ r ∈ range (min i.val j.val + 1),
        (if r ≤ i.val then ρ ^ (i.val - r) else 0) *
          (if r ≤ j.val then ρ ^ (j.val - r) else 0) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : min i.val j.val + 1 ≤ N))
    intro r hr hr'
    by_cases hri : r ≤ i.val
    · have hrj : ¬r ≤ j.val := by
        have := Finset.mem_range.not.mp hr'
        omega
      simp only [if_neg hrj, mul_zero]
    · simp only [if_neg hri, zero_mul]
  rw [hcut]
  apply Finset.sum_congr rfl
  intro r hr
  have hri : r ≤ i.val := by have := Finset.mem_range.mp hr; omega
  have hrj : r ≤ j.val := by have := Finset.mem_range.mp hr; omega
  rw [if_pos hri, if_pos hrj, pow_add]

/-- Two geometric masses pay every row of the complete contraction kernel. -/
theorem geometricContraction_row_le {N : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (i : Fin N) : ∑ j, geometricContraction N ρ i j ≤ ((1 - ρ)⁻¹) ^ 2 := by
  have hK : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hρ1.le)
  calc
    _ = ∑ r : Fin N, geometricLower N ρ i r * ∑ j : Fin N, geometricLower N ρ j r := by
      simp only [geometricContraction, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
    _ ≤ ∑ r : Fin N, geometricLower N ρ i r * (1 - ρ)⁻¹ :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
        (geometricLower_column_le hρ0 hρ1 r) (geometricLower_nonneg hρ0 i r)
    _ = (∑ r : Fin N, geometricLower N ρ i r) * (1 - ρ)⁻¹ := by rw [Finset.sum_mul]
    _ ≤ (1 - ρ)⁻¹ * (1 - ρ)⁻¹ :=
      mul_le_mul_of_nonneg_right (geometricLower_row_le hρ0 hρ1 i) hK
    _ = _ := by ring

/-- Complete-form payment for a weighted source entry bounded by Gaussian contractions. -/
theorem geometricContraction_form_bound {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ)
    (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) {ρ B : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hB : 0 ≤ B)
    (hE : ∀ i j, |E i j| ≤ B * geometricContraction N ρ i j * w i * w j)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ E *ᵥ v| ≤ B * ((1 - ρ)⁻¹) ^ 2 * ∑ i, w i ^ 2 * v i ^ 2 := by
  have he : v ⬝ᵥ E *ᵥ v = ∑ i, ∑ j, v i * E i j * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hrow := GaloisForLFunctions.weighted_double_sum_le_rowBound
    (b := fun i => w i * v i) (geometricContraction_symm N ρ)
    (geometricContraction_nonneg hρ0) (geometricContraction_row_le hρ0 hρ1)
  rw [he]
  calc
    _ ≤ ∑ i, ∑ j, |v i * E i j * v j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ B * ∑ i, ∑ j, |w i * v i| * |w j * v j| * geometricContraction N ρ i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg (v i))) (abs_nonneg (v j))
      simp only [_root_.abs_mul, abs_of_nonneg (hw i), abs_of_nonneg (hw j)]
      nlinarith only [h]
    _ ≤ B * (((1 - ρ)⁻¹) ^ 2 * ∑ i, (w i * v i) ^ 2) :=
      mul_le_mul_of_nonneg_left hrow hB
    _ = _ := by simp only [mul_pow, mul_assoc]

#print axioms geometricContraction_eq_sum
#print axioms geometricContraction_row_le
#print axioms geometricContraction_form_bound

end GaloisForLFunctions.CompletedArithmeticForms
