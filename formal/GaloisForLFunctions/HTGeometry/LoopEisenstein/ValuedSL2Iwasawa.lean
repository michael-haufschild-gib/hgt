import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2RootSplittings
import GaloisForLFunctions.HTGeometry.LoopEisenstein.MatrixValuationContent
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Int.WithZero

/-!
# Rank-one Iwasawa decomposition over a discretely valued field

Choosing the larger-valued bottom-row entry makes the elimination parameter
integral. The resulting determinant-one integral matrix leaves an upper
triangular factor. A triangular integral matrix has unit-valued diagonal.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
open scoped WithZero WithZeroMulInt
noncomputable section
variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- Determinant-one matrices over the valuation integers. -/
def valuationIntegralSL2 : Subgroup (SL2 F) where
  carrier := {g | ∀ i j, v (g i j) ≤ 1}
  one_mem' := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  mul_mem' := by
    intro g h hg hh
    apply (matrixValuationContent_le_iff v _ 1).mp
    change matrixValuationContent v ((g : Matrix (Fin 2) (Fin 2) F) * h) ≤ 1
    exact (matrixValuationContent_mul_le v g h).trans
      (by simpa only [one_mul] using (mul_le_mul'
        ((matrixValuationContent_le_iff v _ 1).mpr hg)
        ((matrixValuationContent_le_iff v _ 1).mpr hh)))
  inv_mem' := by
    intro g hg i j
    change v ((g⁻¹ : SL2 F).1 i j) ≤ 1
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hg 1 1
    · change v (-(g 0 1)) ≤ 1
      rw [Valuation.map_neg]
      exact hg 0 1
    · change v (-(g 1 0)) ≤ 1
      rw [Valuation.map_neg]
      exact hg 1 0
    · exact hg 0 0

private def sl2BottomRowMatrix (g : SL2 F) : Matrix (Fin 2) (Fin 2) F :=
  !![0, 0; g 1 0, g 1 1]

private theorem sl2BottomRowMatrix_mul (g k : SL2 F) :
    sl2BottomRowMatrix (g * k) = sl2BottomRowMatrix g * k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2BottomRowMatrix, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem matrixValuationContent_bottomRow (g : SL2 F) :
    matrixValuationContent v (sl2BottomRowMatrix g) = max (v (g 1 0)) (v (g 1 1)) := by
  simp [matrixValuationContent, sl2BottomRowMatrix]

/-- Integral special-linear multiplication preserves the exact bottom-row valuation. -/
theorem valued_sl2_bottomRow_mul_integral (g k : SL2 F) (hk : k ∈ valuationIntegralSL2 v) :
    max (v ((g * k) 1 0)) (v ((g * k) 1 1)) = max (v (g 1 0)) (v (g 1 1)) := by
  rw [← matrixValuationContent_bottomRow, ← matrixValuationContent_bottomRow,
    sl2BottomRowMatrix_mul]
  apply matrixValuationContent_mul_right_eq v _ k (k⁻¹ : SL2 F)
  · exact (matrixValuationContent_le_iff v _ 1).mpr hk
  · exact (matrixValuationContent_le_iff v _ 1).mpr ((valuationIntegralSL2 v).inv_mem hk)
  · rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]

/-- Every upper-triangular/integral factorization has the same torus valuation. -/
theorem valued_sl2_iwasawa_torus_value (g b k : SL2 F)
    (hb : b 1 0 = 0) (hk : k ∈ valuationIntegralSL2 v) (hbk : b * k = g) :
    v (b 1 1) = max (v (g 1 0)) (v (g 1 1)) := by
  have he := valued_sl2_bottomRow_mul_integral v b k hk
  rw [hbk, hb, map_zero,
    max_eq_right (show (0 : ℤᵐ⁰) ≤ v (b 1 1) from zero_le)] at he
  exact he.symm

private theorem valuation_ratio_le_one {a b : F} (hb : b ≠ 0) (hab : v a ≤ v b) :
    v (a / b) ≤ 1 := by
  rw [Valuation.map_div,
    div_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hb))]
  exact hab

private theorem sl2_bottom_right_ne_zero (g : SL2 F) (hcd : v (g 1 0) ≤ v (g 1 1)) :
    g 1 1 ≠ 0 := by
  intro hd
  have hc : g 1 0 = 0 := by
    have hzero : v (g 1 0) = 0 := le_antisymm
      (by simpa only [hd, map_zero] using hcd) bot_le
    by_contra hne
    exact ((Valuation.ne_zero_iff v).mpr hne) hzero
  have he := SpecialLinearGroup.det_coe g
  rw [det_fin_two, hc, hd, mul_zero, mul_zero, sub_self] at he
  exact zero_ne_one he

/-- Integral lower elimination when the bottom-right entry has maximal value. -/
theorem exists_valued_sl2_upper_integral_of_le (g : SL2 F)
    (hcd : v (g 1 0) ≤ v (g 1 1)) :
    ∃ b k : SL2 F, b 1 0 = 0 ∧ (∀ i j, v (k i j) ≤ 1) ∧ b * k = g ∧
      v (b 1 1) = max (v (g 1 0)) (v (g 1 1)) := by
  have hd := sl2_bottom_right_ne_zero v g hcd
  let t := g 1 0 / g 1 1
  let k := sl2Lower t
  let j := sl2Lower (-t)
  have hjk : j * k = 1 := by
    change sl2Lower (-t) * sl2Lower t = 1
    rw [← sl2Lower_add, neg_add_cancel, sl2Lower_zero]
  refine ⟨g * j, k, ?_, ?_, ?_, ?_⟩
  · change (g * sl2Lower (-t)) 1 0 = 0
    simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    change g 1 0 * 1 + g 1 1 * (-t) = 0
    dsimp only [t]
    field_simp [hd]; ring
  · intro i l
    have ht : v t ≤ 1 := valuation_ratio_le_one v hd hcd
    fin_cases i <;> fin_cases l
    · change v 1 ≤ 1; rw [map_one]
    · change v 0 ≤ 1; rw [map_zero]; exact zero_le_one
    · exact ht
    · change v 1 ≤ 1; rw [map_one]
  · rw [mul_assoc, hjk, mul_one]
  · change v ((g * sl2Lower (-t)) 1 1) = _
    simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    change v (g 1 0 * 0 + g 1 1 * 1) = _
    rw [mul_zero, mul_one, zero_add]
    exact (max_eq_right hcd).symm

/-- Every determinant-one matrix is upper triangular times an integral matrix. -/
theorem exists_valued_sl2_upper_integral (g : SL2 F) :
    ∃ b k : SL2 F, b 1 0 = 0 ∧ (∀ i j, v (k i j) ≤ 1) ∧ b * k = g ∧
      v (b 1 1) = max (v (g 1 0)) (v (g 1 1)) := by
  rcases le_or_gt (v (g 1 0)) (v (g 1 1)) with hcd | hdc
  · exact exists_valued_sl2_upper_integral_of_le v g hcd
  · have hc : g 1 0 ≠ 0 := by
      intro h
      rw [h, map_zero] at hdc
      exact (not_lt_of_ge bot_le) hdc
    let t := g 1 1 / g 1 0
    let k : SL2 F := ⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩
    let j : SL2 F := ⟨!![t, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
    have hjk : j * k = 1 := by
      apply SpecialLinearGroup.ext
      intro i l
      fin_cases i <;> fin_cases l <;>
        simp [j, k, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨g * j, k, ?_, ?_, ?_, ?_⟩
    · simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      change g 1 0 * t + g 1 1 * (-1) = 0
      dsimp only [t]
      field_simp [hc]; ring
    · intro i l
      have ht : v t ≤ 1 := valuation_ratio_le_one v hc hdc.le
      fin_cases i <;> fin_cases l
      · change v 0 ≤ 1; rw [map_zero]; exact zero_le_one
      · change v (-1) ≤ 1; rw [Valuation.map_neg, map_one]
      · change v 1 ≤ 1; rw [map_one]
      · exact ht
    · rw [mul_assoc, hjk, mul_one]
    · simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      change v (g 1 0 * 1 + g 1 1 * 0) = _
      rw [mul_one, mul_zero, add_zero]
      exact (max_eq_left hdc.le).symm

/-- The diagonal of an integral triangular determinant-one matrix consists of valuation units. -/
theorem valued_sl2_triangular_diagonal_value (g : SL2 F)
    (hg : ∀ i j, v (g i j) ≤ 1) (htri : g 1 0 = 0) :
    v (g 0 0) = 1 ∧ v (g 1 1) = 1 := by
  have hdet := SpecialLinearGroup.det_coe g
  rw [det_fin_two, htri, mul_zero, sub_zero] at hdet
  have hprod : v (g 0 0) * v (g 1 1) = 1 := by rw [← map_mul, hdet, map_one]
  constructor
  · apply le_antisymm (hg 0 0)
    calc
      1 = v (g 0 0) * v (g 1 1) := hprod.symm
      _ ≤ v (g 0 0) * 1 := mul_le_mul_left' (hg 1 1) _
      _ = _ := mul_one _
  · apply le_antisymm (hg 1 1)
    calc
      1 = v (g 0 0) * v (g 1 1) := hprod.symm
      _ ≤ 1 * v (g 1 1) := mul_le_mul_right' (hg 0 0) _
      _ = _ := one_mul _

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_valued_sl2_upper_integral
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.valued_sl2_triangular_diagonal_value
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.valued_sl2_bottomRow_mul_integral
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.valued_sl2_iwasawa_torus_value
