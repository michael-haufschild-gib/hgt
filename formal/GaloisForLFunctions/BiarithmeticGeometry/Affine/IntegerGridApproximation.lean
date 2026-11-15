import GaloisForLFunctions.BiarithmeticGeometry.Affine.IntegerWindowCounts

/-!
# Finite integer grids for scaled real intervals

Taking the integer part of a scaled coordinate leaves a remainder in the
unit interval. The integer part lies in an explicit finite window, whose
cardinality grows inversely with the absolute scale.
-/

namespace GaloisForLFunctions.BiarithmeticGeometry.IntegerWindowCounts
noncomputable section

/-- The fractional part belongs to the half-open unit interval. -/
theorem floor_cell_bounds (a : ℝ) :
    0 ≤ a - (⌊a⌋ : ℝ) ∧ a - (⌊a⌋ : ℝ) < 1 := by
  constructor
  · linarith only [Int.floor_le a]
  · linarith only [Int.lt_floor_add_one a]

/-- Rounding down changes absolute magnitude by at most one. -/
theorem abs_floor_le_abs_add_one (a : ℝ) : |(⌊a⌋ : ℝ)| ≤ |a| + 1 := by
  have h := floor_cell_bounds a
  calc
    |(⌊a⌋ : ℝ)| = |a - (a - (⌊a⌋ : ℝ))| := by congr 1; ring
    _ ≤ |a| + |a - (⌊a⌋ : ℝ)| := abs_sub a _
    _ ≤ |a| + 1 := by rw [abs_of_nonneg h.1]; linarith only [h.2]

/-- Every real coordinate has a scaled integer cell with a unit-interval remainder. -/
theorem exists_scaled_integer_cell (q : ℕ) (ε : ℝ) (hε : ε ≠ 0) (β : ℝ) :
    ∃ (i : ℤ) (w : ℝ), 0 ≤ w ∧ w ≤ 1 ∧
      β = ε * ((i : ℝ) / (q + 1 : ℝ) + w) ∧
      |(i : ℝ)| ≤ (q + 1 : ℝ) * |β| / |ε| + 1 := by
  let d : ℝ := q + 1
  let a : ℝ := β * d / ε
  have hd : 0 < d := by dsimp only [d]; positivity
  have hd1 : 1 ≤ d := by
    dsimp only [d]
    linarith only [Nat.cast_nonneg (R := ℝ) q]
  have hf := floor_cell_bounds a
  have he : ε * a = β * d := by
    dsimp only [a]
    rw [mul_comm ε (β * d / ε), div_mul_cancel₀ _ hε]
  refine ⟨⌊a⌋, (a - (⌊a⌋ : ℝ)) / d, div_nonneg hf.1 hd.le, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    simpa only [one_mul] using le_trans hf.2.le hd1
  · change β = ε * ((⌊a⌋ : ℝ) / d + (a - (⌊a⌋ : ℝ)) / d)
    symm
    calc
      _ = (ε * a) / d := by ring
      _ = (β * d) / d := by rw [he]
      _ = (β / d) * d := by ring
      _ = β := div_mul_cancel₀ β (ne_of_gt hd)
  · calc
      |(⌊a⌋ : ℝ)| ≤ |a| + 1 := abs_floor_le_abs_add_one a
      _ = d * |β| / |ε| + 1 := by
        dsimp only [a]
        rw [abs_div, abs_mul, abs_of_pos hd]
        ring

/-- A bounded coordinate can be sampled from an explicit finite integer window. -/
theorem exists_scaled_integer_cell_in_window (q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (β L : ℝ) (hβ : |β| ≤ L) :
    ∃ i ∈ integerWindow 0 ((q + 1 : ℝ) * L / |ε| + 1), ∃ w : ℝ,
      0 ≤ w ∧ w ≤ 1 ∧ β = ε * ((i : ℝ) / (q + 1 : ℝ) + w) := by
  obtain ⟨i, w, hw0, hw1, he, hi⟩ := exists_scaled_integer_cell q ε hε β
  refine ⟨i, ?_, w, hw0, hw1, he⟩
  apply (mem_integerWindow_iff _ _ _).mpr
  simp only [Int.cast_zero, zero_sub, abs_neg]
  exact hi.trans (add_le_add_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hβ (by positivity)) (abs_nonneg ε)) 1)

#print axioms floor_cell_bounds
#print axioms abs_floor_le_abs_add_one
#print axioms exists_scaled_integer_cell
#print axioms exists_scaled_integer_cell_in_window

end
end GaloisForLFunctions.BiarithmeticGeometry.IntegerWindowCounts
