import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearOverlap
import GaloisForLFunctions.BiarithmeticGeometry.Affine.GradedMatrixContraction
import GaloisForLFunctions.BiarithmeticGeometry.Affine.MatrixCubeBounds

/-!
# Bounded selected-coordinate inverses for balanced shear blocks

The retained original coordinates fix the lower rows of the inverse matrix.
The selected transformed coordinates fix the upper rows of its product with
the shear. For balanced blocks the remaining entries have nonpositive
integer weights. Diagonal rescaling therefore bounds both matrices uniformly
for absolute shear at least one.
-/

open MeasureTheory Matrix
open scoped ENNReal
open GaloisForLFunctions.BiarithmeticGeometry
open MixedCoordinateVolume MatrixCubeBounds

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The selected-coordinate matrix in the original ambient ordering. -/
def shearSelected (q r : ℕ) (θ : ℝ) : Matrix (Fin (2 * q + r)) (Fin (2 * q + r)) ℝ :=
  selectedMatrix (shearBlock (2 * q + r) θ) (shearSelector q r)

/-- The monomial weight of each original coordinate. -/
def shearWeight {m : ℕ} (i : Fin m) : ℤ := i.val

/-- The monomial weight of the coordinate chosen in each selected row. -/
def shearSelectedWeight (q r : ℕ) (i : Fin (2 * q + r)) : ℤ :=
  Sum.elim shearWeight shearWeight (shearSelector q r i)

/-- Large-shear right inverse obtained by rescaling the fixed inverse at shear one. -/
def shearSelectedInverse (q r : ℕ) (θ : ℝ) :
    Matrix (Fin (2 * q + r)) (Fin (2 * q + r)) ℝ :=
  GradedMatrix.scale θ shearWeight (shearSelectedWeight q r) (shearSelected q r 1)⁻¹

private theorem shearBlock_eq_scale (m : ℕ) (θ : ℝ) :
    shearBlock m θ = GradedMatrix.scale θ shearWeight shearWeight (shearBlock m 1) := by
  ext i j
  by_cases hij : j.val ≤ i.val
  · simp only [shearBlock, GradedMatrix.scale, shearWeight, one_pow, mul_one]
    rw [← Int.natCast_sub hij, zpow_natCast, mul_comm]
  · have hz := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hij)
    simp only [shearBlock, GradedMatrix.scale, hz, Nat.cast_zero, zero_mul, mul_zero]

private theorem selectedMatrix_scale {m : ℕ} (θ : ℝ) (w : Fin m → ℤ)
    (M : Matrix (Fin m) (Fin m) ℝ) (s : Fin m → Fin m ⊕ Fin m) :
    selectedMatrix (GradedMatrix.scale θ w w M) s =
      GradedMatrix.scale θ (fun i => Sum.elim w w (s i)) w (selectedMatrix M s) := by
  ext i j
  cases hs : s i with
  | inl k =>
    simp only [selectedMatrix, hs, Sum.elim_inl, GradedMatrix.scale]
    by_cases h : k = j
    · subst j
      simp only [Matrix.one_apply, ite_true, sub_self, zpow_zero, one_mul]
    · simp only [Matrix.one_apply, h, ite_false, mul_zero]
  | inr k => simp only [selectedMatrix, hs, Sum.elim_inr, GradedMatrix.scale]

private theorem shearSelected_eq_scale (q r : ℕ) (θ : ℝ) :
    shearSelected q r θ = GradedMatrix.scale θ (shearSelectedWeight q r) shearWeight
      (shearSelected q r 1) := by
  rw [shearSelected, shearBlock_eq_scale _ θ, selectedMatrix_scale]
  rfl

private theorem shearSelected_one_det_ne_zero (q r : ℕ) :
    (shearSelected q r 1).det ≠ 0 := by
  simpa only [shearSelected, det_shear_selectedMatrix, one_pow, mul_one] using
    shearMinorConstant_ne_zero q r

/-- The rescaled fixed inverse is an actual right inverse of the selected coordinates. -/
theorem shearSelected_mul_inverse (q r : ℕ) (θ : ℝ) (hθ : θ ≠ 0) :
    shearSelected q r θ * shearSelectedInverse q r θ = 1 := by
  rw [shearSelected_eq_scale q r θ, shearSelectedInverse]
  exact GradedMatrix.scale_right_inverse θ hθ _ _ _ _
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (shearSelected_one_det_ne_zero q r)))

/-- Transforming the right inverse leaves a fixed matrix with rescaled entries. -/
theorem shearBlock_mul_selectedInverse (q r : ℕ) (θ : ℝ) (hθ : θ ≠ 0) :
    shearBlock (2 * q + r) θ * shearSelectedInverse q r θ =
      GradedMatrix.scale θ shearWeight (shearSelectedWeight q r)
        (shearBlock (2 * q + r) 1 * (shearSelected q r 1)⁻¹) := by
  rw [shearBlock_eq_scale _ θ, shearSelectedInverse, GradedMatrix.scale_mul θ hθ]

private theorem selectedWeight_inl (q r : ℕ) (i : Fin q) :
    shearSelectedWeight q r (shearSplit q r (Sum.inl i)) = (q + r + i.val : ℕ) := by
  simp only [shearSelectedWeight, shearSelector, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr]
  rfl

private theorem selectedWeight_inr (q r : ℕ) (i : Fin (q + r)) :
    shearSelectedWeight q r (shearSplit q r (Sum.inr i)) =
      shearWeight (shearSplit q r (Sum.inr i)) := by
  simp only [shearSelectedWeight, shearSelector, Equiv.symm_apply_apply, Sum.elim_inr,
    Sum.elim_inl]

private theorem selectedWeight_ge (q r : ℕ) (i : Fin (2 * q + r)) :
    (q : ℤ) ≤ shearSelectedWeight q r i := by
  obtain ⟨i, rfl⟩ := (shearSplit q r).surjective i
  rcases i with i | i
  · rw [selectedWeight_inl]
    omega
  · rw [selectedWeight_inr]
    change (q : ℤ) ≤ ((q + i.val : ℕ) : ℤ)
    omega

private theorem selected_row_inl (q r : ℕ) (θ : ℝ) (i : Fin q)
    (j : Fin (2 * q + r)) :
    shearSelected q r θ (shearSplit q r (Sum.inl i)) j =
      shearBlock (2 * q + r) θ (shearMinorRows q r i) j := by
  simp only [shearSelected, selectedMatrix, shearSelector, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr]

private theorem selected_row_inr (q r : ℕ) (θ : ℝ) (i : Fin (q + r))
    (j : Fin (2 * q + r)) :
    shearSelected q r θ (shearSplit q r (Sum.inr i)) j =
      (1 : Matrix (Fin (2 * q + r)) (Fin (2 * q + r)) ℝ)
        (shearSplit q r (Sum.inr i)) j := by
  simp only [shearSelected, selectedMatrix, shearSelector, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr]

private theorem inverse_retained_row (q r : ℕ) (i : Fin (q + r))
    (j : Fin (2 * q + r)) :
    (shearSelected q r 1)⁻¹ (shearSplit q r (Sum.inr i)) j =
      (1 : Matrix (Fin (2 * q + r)) (Fin (2 * q + r)) ℝ)
        (shearSplit q r (Sum.inr i)) j := by
  calc
    _ = ((1 : Matrix (Fin (2 * q + r)) (Fin (2 * q + r)) ℝ) *
        (shearSelected q r 1)⁻¹) (shearSplit q r (Sum.inr i)) j := by rw [one_mul]
    _ = (shearSelected q r 1 * (shearSelected q r 1)⁻¹)
        (shearSplit q r (Sum.inr i)) j := by simp only [Matrix.mul_apply, selected_row_inr]
    _ = _ := by rw [Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (shearSelected_one_det_ne_zero q r))]

private theorem transformed_inverse_selected_row (q r : ℕ) (i : Fin q)
    (j : Fin (2 * q + r)) :
    (shearBlock (2 * q + r) 1 * (shearSelected q r 1)⁻¹) (shearMinorRows q r i) j =
      (1 : Matrix (Fin (2 * q + r)) (Fin (2 * q + r)) ℝ)
        (shearSplit q r (Sum.inl i)) j := by
  calc
    _ = (shearSelected q r 1 * (shearSelected q r 1)⁻¹)
        (shearSplit q r (Sum.inl i)) j := by simp only [Matrix.mul_apply, selected_row_inl]
    _ = _ := by rw [Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (shearSelected_one_det_ne_zero q r))]

private theorem inverse_weight_support (q r : ℕ) (i j : Fin (2 * q + r))
    (hij : (shearSelected q r 1)⁻¹ i j ≠ 0) :
    shearWeight i ≤ shearSelectedWeight q r j := by
  obtain ⟨i, rfl⟩ := (shearSplit q r).surjective i
  rcases i with i | i
  · have hw : shearWeight (shearSplit q r (Sum.inl i)) = (i.val : ℤ) := rfl
    rw [hw]
    have hle : (i.val : ℤ) ≤ q := by exact_mod_cast i.isLt.le
    exact hle.trans (selectedWeight_ge q r j)
  · have he : shearSplit q r (Sum.inr i) = j := by
      by_contra h
      apply hij
      rw [inverse_retained_row, Matrix.one_apply, if_neg h]
    subst j
    exact (selectedWeight_inr q r i).ge

private theorem transformed_inverse_weight_support (q r : ℕ) (hr : r ≤ 1)
    (i j : Fin (2 * q + r))
    (hij : (shearBlock (2 * q + r) 1 * (shearSelected q r 1)⁻¹) i j ≠ 0) :
    shearWeight i ≤ shearSelectedWeight q r j := by
  by_cases hi : i.val < q + r
  · have hlow : shearWeight i ≤ (q : ℤ) := by dsimp [shearWeight]; omega
    exact hlow.trans (selectedWeight_ge q r j)
  · let k : Fin q := ⟨i.val - (q + r), by omega⟩
    have hk : shearMinorRows q r k = i := by apply Fin.ext; dsimp [shearMinorRows, k]; omega
    have he : shearSplit q r (Sum.inl k) = j := by
      by_contra h
      apply hij
      rw [← hk, transformed_inverse_selected_row, Matrix.one_apply, if_neg h]
    subst j
    rw [selectedWeight_inl, ← hk]
    exact le_rfl

/-- Every entry of the selected right inverse is uniformly bounded at large shear. -/
theorem abs_shearSelectedInverse_le (q r : ℕ) (θ : ℝ) (hθ : 1 ≤ |θ|)
    (i j : Fin (2 * q + r)) :
    |shearSelectedInverse q r θ i j| ≤ |(shearSelected q r 1)⁻¹ i j| :=
  GradedMatrix.abs_scale_le θ hθ _ _ _ (inverse_weight_support q r) i j

/-- In balanced blocks the transformed inverse has the same uniform entrywise bound. -/
theorem abs_shearBlock_mul_selectedInverse_le (q r : ℕ) (hr : r ≤ 1)
    (θ : ℝ) (hθ : 1 ≤ |θ|) (i j : Fin (2 * q + r)) :
    |(shearBlock (2 * q + r) θ * shearSelectedInverse q r θ) i j| ≤
      |(shearBlock (2 * q + r) 1 * (shearSelected q r 1)⁻¹) i j| := by
  have hn : θ ≠ 0 := by intro hz; rw [hz, abs_zero] at hθ; norm_num at hθ
  rw [shearBlock_mul_selectedInverse q r θ hn]
  exact GradedMatrix.abs_scale_le θ hθ _ _ _
    (transformed_inverse_weight_support q r hr) i j

#print axioms shearSelected_mul_inverse
#print axioms shearBlock_mul_selectedInverse
#print axioms abs_shearSelectedInverse_le
#print axioms abs_shearBlock_mul_selectedInverse_le

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
