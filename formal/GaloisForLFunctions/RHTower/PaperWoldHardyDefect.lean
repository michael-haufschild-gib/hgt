import GaloisForLFunctions.RHTower.PaperWoldCompositeOperator

/-! # The exact arithmetic deficit from the half Hardy tail

Both the row-factor error and the logarithmic-cell error have a square-summable
product majorant. The original composite coefficients are retained throughout.
-/

namespace RHTower
noncomputable section

private def compositeCell (n : ℕ) : ℝ := -xiHeatCassiniWoldNatIncrement (2 * n + 2)
private def compositeRow (n : ℕ) : ℝ := (2 * (n : ℝ) + 3) * compositeCell n

private theorem cell_nonneg (n : ℕ) : 0 ≤ compositeCell n :=
  neg_nonneg.mpr (paperWold_even_composite_increment_neg n).le

private theorem cell_inv_le (n : ℕ) : compositeCell n ≤ 1 / ((n : ℝ) + 1) :=
  (paperWold_even_composite_increment_upper n).trans
    (one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n]))

private theorem row_le_one (n : ℕ) : compositeRow n ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (paperWold_even_composite_increment_upper n)
    (by positivity : 0 ≤ 2 * (n : ℝ) + 3)
  simpa only [compositeRow, compositeCell,
    mul_one_div_cancel (by positivity : 2 * (n : ℝ) + 3 ≠ 0)] using h

private theorem row_defect_le (n : ℕ) : 1 - compositeRow n ≤ 1 / ((n : ℝ) + 1) := by
  have h := mul_le_mul_of_nonneg_left (paperWold_even_composite_increment_lower n)
    (by positivity : 0 ≤ 2 * (n : ℝ) + 3)
  have he : (2 * (n : ℝ) + 3) * (1 / (2 * n + 4)) = 1 - 1 / (2 * n + 4) := by
    field_simp
    ring
  rw [he] at h
  have hb : 1 - compositeRow n ≤ 1 / (2 * (n : ℝ) + 4) := by
    change 1 - (2 * (n : ℝ) + 3) * (-xiHeatCassiniWoldNatIncrement (2 * n + 2)) ≤ _
    linarith
  exact hb.trans (one_div_le_one_div_of_le (by positivity)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]))

private theorem cell_hardy_defect (j : ℕ) :
    0 ≤ 1 / (2 * ((j : ℝ) + 1)) - compositeCell j ∧
      1 / (2 * ((j : ℝ) + 1)) - compositeCell j ≤ (1 / ((j : ℝ) + 1)) ^ 2 := by
  constructor
  · apply sub_nonneg.mpr
    exact (paperWold_even_composite_increment_upper j).trans
      (one_div_le_one_div_of_le (by positivity) (by linarith))
  · calc
      _ ≤ 1 / (2 * ((j : ℝ) + 1)) - 1 / (2 * j + 4) := by
        have h := paperWold_even_composite_increment_lower j
        change 1 / (2 * ((j : ℝ) + 1)) - (-xiHeatCassiniWoldNatIncrement (2 * j + 2)) ≤ _
        linarith
      _ = 1 / (2 * ((j : ℝ) + 1) * (j + 2)) := by field_simp; ring
      _ ≤ 1 / (((j : ℝ) + 1) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
      _ = _ := by rw [div_pow, one_pow]

private theorem composite_hardy_defect_bounds (n j : ℕ) (hnj : n < j) :
    0 ≤ 1 / (2 * ((j : ℝ) + 1)) - compositeRow n * compositeCell j ∧
      1 / (2 * ((j : ℝ) + 1)) - compositeRow n * compositeCell j ≤
        2 * (1 / ((n : ℝ) + 1)) * (1 / ((j : ℝ) + 1)) := by
  have he : 1 / (2 * ((j : ℝ) + 1)) - compositeRow n * compositeCell j =
      (1 - compositeRow n) * compositeCell j +
        (1 / (2 * ((j : ℝ) + 1)) - compositeCell j) := by ring
  rw [he]
  have hcell := cell_hardy_defect j
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr (row_le_one n)) (cell_nonneg j)) hcell.1
  · have hj : (1 / ((j : ℝ) + 1)) ^ 2 ≤
        (1 / ((n : ℝ) + 1)) * (1 / ((j : ℝ) + 1)) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right
        (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnj.le 1))
        (by positivity)
    have hrow := mul_le_mul (row_defect_le n) (cell_inv_le j) (cell_nonneg j)
      (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))
    calc
      _ ≤ (1 / ((n : ℝ) + 1)) * (1 / ((j : ℝ) + 1)) +
          (1 / ((n : ℝ) + 1)) * (1 / ((j : ℝ) + 1)) := add_le_add hrow (hcell.2.trans hj)
      _ = _ := by ring

/-- Half the strictly upper Hardy tail, in the exact native index normalization. -/
def paperWoldHardyEntry (n j : ℕ) : ℂ :=
  if n < j then ((1 / (2 * ((j : ℝ) + 1)) : ℝ) : ℂ) else 0

def paperWoldHardyDefect (q : ℕ × ℕ) : ℂ :=
  paperWoldHardyEntry q.1 q.2 - paperWoldCompositeEntry (1 / 2) q.1 q.2

theorem paperWoldHardyDefect_re_nonneg (q : ℕ × ℕ) : 0 ≤ (paperWoldHardyDefect q).re := by
  rw [paperWoldHardyDefect, paperWoldHardyEntry, paperWoldCompositeEntry_critical_formula]
  by_cases h : q.1 < q.2
  · simp only [if_pos h, Complex.sub_re, Complex.ofReal_re]
    exact (composite_hardy_defect_bounds q.1 q.2 h).1
  · simp only [if_neg h, sub_self, Complex.zero_re, le_refl]

theorem paperWoldHardyDefect_bound (q : ℕ × ℕ) :
    ‖paperWoldHardyDefect q‖ ≤
      2 * (1 / ((q.1 : ℝ) + 1)) * (1 / ((q.2 : ℝ) + 1)) := by
  rw [paperWoldHardyDefect, paperWoldHardyEntry, paperWoldCompositeEntry_critical_formula]
  by_cases h : q.1 < q.2
  · simp only [if_pos h, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hb := composite_hardy_defect_bounds q.1 q.2 h
    dsimp only [compositeRow, compositeCell] at hb
    rw [abs_of_nonneg hb.1]
    exact hb.2
  · simp only [if_neg h, sub_self, norm_zero]
    positivity

theorem paperWoldHardyDefect_isHS : HilbertSchmidt.IsHS paperWoldHardyDefect := by
  have hs : Summable (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2) := by
    have h := ((Real.summable_nat_rpow).mpr (by norm_num : (-2 : ℝ) < -1)).comp_injective
      Nat.succ_injective
    refine h.congr fun n => ?_
    simp only [Function.comp_def, Nat.cast_succ]
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [one_div, inv_pow]
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    ((hs.mul_of_nonneg hs (fun n => sq_nonneg _) (fun n => sq_nonneg _)).mul_left 4)
  calc
    _ ≤ (2 * (1 / ((q.1 : ℝ) + 1)) * (1 / ((q.2 : ℝ) + 1))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (paperWoldHardyDefect_bound q) 2
    _ = _ := by ring

end
end RHTower
