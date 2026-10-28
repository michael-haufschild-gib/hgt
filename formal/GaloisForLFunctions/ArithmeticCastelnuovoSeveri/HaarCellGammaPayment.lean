import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanZeroCoercivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellProfiles

/-!
# Gamma payment for balanced complete-cell sections

Adjacent pairs have width `log(1 + 1/a)` and zero mean. Their original Gamma
energy therefore pays `log a` times their exact square mass, with no loss
depending on the upper support horizon or on the signs of the coefficients.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry MeanZeroIntervals

/-- An adjacent pair has the same logarithmic width as the cell at half its lower index. -/
theorem haarPairWidth {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ) = logCellWidth a := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [show 2 * (a : ℝ) + 2 = 2 * ((a : ℝ) + 1) by ring,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (a : ℝ) + 1 ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne']
  unfold logCellWidth
  ring

/-- Arbitrary signed balanced sections retain the full logarithmic Gamma coefficient. -/
theorem haarSectionProfile_levyEnergy_ge (c : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * c a ^ 2) ≤
      levyEnergy (haarSectionProfile c X) := by
  let S := Finset.Icc 1 X
  let L : S → ℝ := fun i => Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hwidth (i : S) : U i - L i = logCellWidth (i : ℕ) := haarPairWidth (hpos i)
  have hw0 (i : S) : 0 < U i - L i := by rw [hwidth]; exact logCellWidth_pos (hpos i)
  have hwidth1 (i : S) : U i - L i ≤ 1 := by
    rw [hwidth]
    exact (logCellWidth_le_inv (hpos i)).trans
      ((div_le_one (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))).mpr
        (by exact_mod_cast hpos i))
  have hsep (i j : S) (hij : i ≠ j) : U i ≤ L j ∨ U j ≤ L i := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      apply Real.log_le_log (by have := hpos i; positivity)
      exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega)
    · right
      apply Real.log_le_log (by have := hpos j; positivity)
      exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega)
  have h := levyEnergy_ge_sum_log_width L U (fun i => sub_pos.mp (hw0 i)) hwidth1 hsep
    (haarSectionProfile_bv c X) (haarSectionProfile_compact c X)
    (fun i => setIntegral_haarSectionProfile_pair c (hpos i) (Finset.mem_Icc.mp i.property).2)
  apply le_trans ?_ h
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_le_sum
  intro i _hi
  rw [setIntegral_haarSectionProfile_pair_sq c (hpos i) (Finset.mem_Icc.mp i.property).2]
  have hlog : Real.log ((i : ℕ) : ℝ) ≤ Real.log (1 / (U i - L i)) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))
    apply (le_div_iff₀ (hw0 i)).mpr
    rw [hwidth]
    have hle := mul_le_mul_of_nonneg_left (logCellWidth_le_inv (hpos i))
      (Nat.cast_nonneg (i : ℕ))
    have hi0 : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show (i : ℕ) ≠ 0 by have := hpos i; omega)
    simpa only [mul_one_div_cancel hi0] using hle
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlog
    (mul_nonneg (haarMass_pos (hpos i)).le (sq_nonneg _))

#print axioms haarPairWidth
#print axioms haarSectionProfile_levyEnergy_ge

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
