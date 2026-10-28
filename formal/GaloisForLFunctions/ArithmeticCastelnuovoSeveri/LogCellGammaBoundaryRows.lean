import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCellGammaRowGeometry
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaExteriorSubsets

/-!
# Uniform touching-cell Gamma losses

The two adjacent intervals cost at most four fixed exponential units per
source width. The bottom cell has no lower neighbor.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry MeanZeroIntervals

private theorem shifted_logCell_width (s : ℝ) (a : ℕ) :
    (s + Real.log ((a + 1 : ℕ) : ℝ)) - (s + Real.log (a : ℝ)) = logCellWidth a := by
  simp only [add_sub_add_left_eq_sub, logCellWidth, Nat.cast_add, Nat.cast_one]

/-- The upper touching-cell replacement loss costs at most three half-exponential units. -/
theorem gamma_logCell_upper_adjacent_le {a : ℕ} (ha : 1 ≤ a) (s : ℝ) :
    gammaIntervalPairDefect (s + Real.log (a : ℝ)) (s + Real.log ((a + 1 : ℕ) : ℝ))
      (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log ((a + 1 + 1 : ℕ) : ℝ)) ≤
      ENNReal.ofReal ((3 / 2) * Real.exp (1 / 2) * logCellWidth a) := by
  have hw0 := logCellWidth_pos ha
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hw1 : logCellWidth a ≤ 1 := (logCellWidth_le_inv ha).trans
    ((div_le_one ha0).mpr (by exact_mod_cast ha))
  have hab : s + Real.log (a : ℝ) < s + Real.log ((a + 1 : ℕ) : ℝ) := by
    apply sub_pos.mp
    rw [shifted_logCell_width]
    exact hw0
  have h := gammaIntervalPairDefect_le_boundary hab
    (by rwa [shifted_logCell_width]) (Or.inl (le_refl (s + Real.log ((a + 1 : ℕ) : ℝ))))
    (d := s + Real.log ((a + 1 + 1 : ℕ) : ℝ))
  simp only [shifted_logCell_width] at h
  have hmass := mul_le_mul_of_nonneg_left (gamma_upper_adjacent_far_mass_le ha) hw0.le
  have hkp : 0 ≤ archLevyDensity (logCellWidth a) := (archLevyDensity_pos hw0).le
  refine h.trans ?_
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Real.exp (1 / 2) * logCellWidth a)
    (mul_nonneg (mul_nonneg hw0.le (logCellWidth_pos (by omega)).le) hkp)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith only [hmass])

/-- The lower touching-cell replacement loss costs at most five half-exponential units. -/
theorem gamma_logCell_lower_adjacent_le {a : ℕ} (ha : 1 ≤ a) (s : ℝ) :
    gammaIntervalPairDefect (s + Real.log (a : ℝ)) (s + Real.log ((a + 1 : ℕ) : ℝ))
      (s + Real.log ((a - 1 : ℕ) : ℝ)) (s + Real.log ((a - 1 + 1 : ℕ) : ℝ)) ≤
      ENNReal.ofReal ((5 / 2) * Real.exp (1 / 2) * logCellWidth a) := by
  by_cases ha2 : 2 ≤ a
  · have hw0 := logCellWidth_pos ha
    have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
    have hw1 : logCellWidth a ≤ 1 := (logCellWidth_le_inv ha).trans
      ((div_le_one ha0).mpr (by exact_mod_cast ha))
    have hab : s + Real.log (a : ℝ) < s + Real.log ((a + 1 : ℕ) : ℝ) := by
      apply sub_pos.mp
      rw [shifted_logCell_width]
      exact hw0
    have hsep : s + Real.log ((a - 1 + 1 : ℕ) : ℝ) ≤ s + Real.log (a : ℝ) := by
      rw [show a - 1 + 1 = a by omega]
    have h := gammaIntervalPairDefect_le_boundary hab
      (by rwa [shifted_logCell_width]) (Or.inr hsep)
      (c := s + Real.log ((a - 1 : ℕ) : ℝ))
    simp only [shifted_logCell_width] at h
    have hmass := mul_le_mul_of_nonneg_left (gamma_lower_adjacent_far_mass_le ha2) hw0.le
    have hkp : 0 ≤ archLevyDensity (logCellWidth a) := (archLevyDensity_pos hw0).le
    refine h.trans ?_
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Real.exp (1 / 2) * logCellWidth a)
      (mul_nonneg (mul_nonneg hw0.le (logCellWidth_pos (by omega)).le) hkp)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith only [hmass])
  · have haeq : a = 1 := by omega
    subst a
    simp only [Nat.sub_self, Nat.cast_zero, Real.log_zero, Nat.zero_add,
      Nat.cast_one, Real.log_one, add_zero, gammaIntervalPairDefect, gammaIntervalKernel,
      Ioo_self, Measure.restrict_empty, lintegral_zero_measure, lintegral_zero, zero_tsub]
    exact bot_le

/-- Every finite adjacent row has a horizon-independent four-exponential bound. -/
theorem gamma_logCell_adjacent_sum_le {a : ℕ} (ha : 1 ≤ a) (s : ℝ) (S : Finset ℕ)
    (hS : ∀ b ∈ S, b + 1 = a ∨ a + 1 = b) :
    (∑ b ∈ S, gammaIntervalPairDefect (s + Real.log (a : ℝ))
      (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log (b : ℝ))
      (s + Real.log ((b + 1 : ℕ) : ℝ))) ≤
      ENNReal.ofReal (4 * Real.exp (1 / 2) * logCellWidth a) := by
  let P : ℕ → ℝ≥0∞ := fun b => gammaIntervalPairDefect (s + Real.log (a : ℝ))
    (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log (b : ℝ)) (s + Real.log ((b + 1 : ℕ) : ℝ))
  have hsub : S ⊆ {a - 1, a + 1} := by
    intro b hb
    rcases hS b hb with hl | hr
    · have he : b = a - 1 := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton, he, true_or]
    · simp only [Finset.mem_insert, Finset.mem_singleton, hr, or_true]
  have hw : 0 ≤ logCellWidth a := (logCellWidth_pos ha).le
  calc
    _ ≤ ∑ b ∈ ({a - 1, a + 1} : Finset ℕ), P b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => bot_le
    _ = P (a - 1) + P (a + 1) := by
      rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
    _ ≤ ENNReal.ofReal ((5 / 2) * Real.exp (1 / 2) * logCellWidth a) +
        ENNReal.ofReal ((3 / 2) * Real.exp (1 / 2) * logCellWidth a) :=
      add_le_add (gamma_logCell_lower_adjacent_le ha s) (gamma_logCell_upper_adjacent_le ha s)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

#print axioms gamma_logCell_upper_adjacent_le
#print axioms gamma_logCell_lower_adjacent_le
#print axioms gamma_logCell_adjacent_sum_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
