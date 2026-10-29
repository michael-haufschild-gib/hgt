import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2WeylLifts

/-!
# Four elementary pivot reductions in SL₂

An invertible entry reduces a determinant-one matrix to a diagonal or Weyl
matrix using two explicit shears. Keeping the upper and lower shear types
separate permits valuation-sensitive elimination in an Iwahori subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {K : Type*} [Field K]

theorem sl2WeylLower_mul_diagonal (a b : Kˣ) :
    sl2WeylLower a * sl2Diagonal b = sl2WeylLower (a * b) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Eliminate about the upper-left entry using a lower and an upper shear. -/
theorem sl2_pivot_upper_left (g : SL2 K) (a : Kˣ) (ha : g 0 0 = (a : K)) :
    sl2Lower (-g 1 0 / (a : K)) * g * sl2Upper (-g 0 1 / (a : K)) = sl2Diagonal a := by
  have hd := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, ha] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, sl2Upper, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, ha, Units.val_inv_eq_inv_val, a.ne_zero]
  field_simp
  linear_combination hd

/-- Eliminate about the lower-right entry using an upper and a lower shear. -/
theorem sl2_pivot_lower_right (g : SL2 K) (a : Kˣ) (ha : g 1 1 = (a : K)) :
    sl2Upper (-g 0 1 / (a : K)) * g * sl2Lower (-g 1 0 / (a : K)) = sl2Diagonal a⁻¹ := by
  have hd := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, ha] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, sl2Upper, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, ha, Units.val_inv_eq_inv_val, a.ne_zero]
  field_simp
  linear_combination hd

/-- Eliminate about the lower-left entry using two upper shears. -/
theorem sl2_pivot_lower_left (g : SL2 K) (a : Kˣ) (ha : g 1 0 = (a : K)) :
    sl2Upper (-g 0 0 / (a : K)) * g * sl2Upper (-g 1 1 / (a : K)) = sl2WeylLower a := by
  have hd := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, ha] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, sl2WeylLower, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, ha, Units.val_inv_eq_inv_val, a.ne_zero]
  field_simp
  linear_combination -hd

/-- Eliminate about the upper-right entry using two lower shears. -/
theorem sl2_pivot_upper_right (g : SL2 K) (a : Kˣ) (ha : g 0 1 = (a : K)) :
    sl2Lower (-g 1 1 / (a : K)) * g * sl2Lower (-g 0 0 / (a : K)) = sl2WeylLower (-a⁻¹) := by
  have hd := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, ha] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, sl2WeylLower, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, ha, Units.val_inv_eq_inv_val, a.ne_zero]
  field_simp
  linear_combination -hd

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
