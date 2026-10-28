import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellGammaPayment

/-!
# Adjacent and distant logarithmic Gamma rows

The far-end kernel has no touching singularity. Neighboring cell widths pay
its boundary reading uniformly, while distant cells have a fixed logarithmic gap.
-/

noncomputable section
open Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry SpacingScaleHarmonicAnalysis

/-- The Gamma reading at one cell width grows at most linearly in its index. -/
theorem gamma_logCellWidth_le {a : ℕ} (ha : 1 ≤ a) :
    archLevyDensity (logCellWidth a) ≤ Real.exp (1 / 2) * ((a : ℝ) + 1) / 2 := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hw0 := logCellWidth_pos ha
  have hw1 : logCellWidth a ≤ 1 := (logCellWidth_le_inv ha).trans
    ((div_le_one ha0).mpr (by exact_mod_cast ha))
  have hmul := mul_le_mul_of_nonneg_left (inv_add_one_le_logCellWidth ha)
    (by positivity : 0 ≤ (a : ℝ) + 1)
  have he : ((a : ℝ) + 1) * (1 / ((a : ℝ) + 1)) = 1 := by field_simp
  rw [he] at hmul
  have hscaled := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (1 / 2)).le
  refine (archLevyDensity_le_sqrt_e_div hw0 hw1).trans ?_
  apply (div_le_iff₀ (mul_pos (by norm_num) hw0)).mpr
  nlinarith only [hscaled]

/-- The upper adjacent far-charge row has a uniform half-exponential bound. -/
theorem gamma_upper_adjacent_far_mass_le {a : ℕ} (ha : 1 ≤ a) :
    logCellWidth (a + 1) * archLevyDensity (logCellWidth a) ≤ Real.exp (1 / 2) / 2 := by
  have hkp := (archLevyDensity_pos (logCellWidth_pos ha)).le
  calc
    _ ≤ (1 / ((a + 1 : ℕ) : ℝ)) * (Real.exp (1 / 2) * ((a : ℝ) + 1) / 2) :=
      mul_le_mul (logCellWidth_le_inv (by omega)) (gamma_logCellWidth_le ha) hkp (by positivity)
    _ = _ := by
      rw [Nat.cast_add, Nat.cast_one]
      field_simp

/-- The lower adjacent far-charge row also has a uniform bound. -/
theorem gamma_lower_adjacent_far_mass_le {a : ℕ} (ha : 2 ≤ a) :
    logCellWidth (a - 1) * archLevyDensity (logCellWidth a) ≤
      (3 / 2) * Real.exp (1 / 2) := by
  have hm : 1 ≤ a - 1 := by omega
  have ha1 : 1 ≤ a := by omega
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hm0 : (0 : ℝ) < ((a - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hkp := (archLevyDensity_pos (logCellWidth_pos ha1)).le
  calc
    _ ≤ (1 / ((a - 1 : ℕ) : ℝ)) * (Real.exp (1 / 2) * ((a : ℝ) + 1) / 2) :=
      mul_le_mul (logCellWidth_le_inv hm) (gamma_logCellWidth_le ha1) hkp (by positivity)
    _ = (Real.exp (1 / 2) * ((a : ℝ) + 1) / 2) / ((a - 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := by
      apply (div_le_iff₀ hm0).mpr
      rw [Nat.cast_sub ha1, Nat.cast_one]
      have h := mul_nonneg (Real.exp_pos (1 / 2)).le (sub_nonneg.mpr haR)
      nlinarith only [h]

/-- Cells beyond a factor of two lie beyond a fixed positive logarithmic gap. -/
theorem logCell_distant_subset {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hfar : 2 * b < a ∨ 2 * a < b) :
    Ioo (Real.log (b : ℝ)) (Real.log (((b + 1 : ℕ) : ℝ))) ⊆
      Iio (Real.log (a : ℝ) - Real.log (3 / 2 : ℝ)) ∪
        Ioi (Real.log (((a + 1 : ℕ) : ℝ)) + Real.log (3 / 2 : ℝ)) := by
  intro y hy
  rcases hfar with hleft | hright
  · left
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hfarR : 2 * (b : ℝ) + 1 ≤ a := by exact_mod_cast (show 2 * b + 1 ≤ a by omega)
    have hlog : Real.log (((b + 1 : ℕ) : ℝ)) + Real.log (3 / 2 : ℝ) ≤ Real.log (a : ℝ) := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      apply Real.log_le_log (by positivity)
      push_cast
      nlinarith only [hbR, hfarR]
    change y < Real.log (a : ℝ) - Real.log (3 / 2 : ℝ)
    linarith only [hy.2, hlog]
  · right
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hfarR : 2 * (a : ℝ) + 1 ≤ b := by exact_mod_cast (show 2 * a + 1 ≤ b by omega)
    have hlog : Real.log (((a + 1 : ℕ) : ℝ)) + Real.log (3 / 2 : ℝ) ≤ Real.log (b : ℝ) := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      apply Real.log_le_log (by positivity)
      push_cast
      nlinarith only [haR, hfarR]
    exact hlog.trans_lt hy.1

#print axioms gamma_logCellWidth_le
#print axioms gamma_upper_adjacent_far_mass_le
#print axioms gamma_lower_adjacent_far_mass_le
#print axioms logCell_distant_subset

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
