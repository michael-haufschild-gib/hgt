import GaloisForLFunctions.ArithmeticIndexDescent.ThePrimeTwoMixedBlockReadsCoarseDifferences
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVarianceRemainder

/-!
# Gamma pays differences of adjacent coarse means

The variance on two merged intervals contains the parallel mass times the
square difference of their means. Applied to complete logarithmic cells,
this retains the original detail profile while charging adjacent coarse
differences. Disjoint merged intervals give a logarithmic Gamma payment.
-/

noncomputable section

open MeasureTheory Set Filter
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells ArithmeticCastelnuovoSeveri.IntervalVariance
open BiarithmeticGaugeGeometry HTGeometry

private theorem parallelMass_square_le (u v x y t : ℝ) (hu : 0 < u) (hv : 0 < v) :
    u * v / (u + v) * (x - y) ^ 2 ≤ u * (x - t) ^ 2 + v * (y - t) ^ 2 := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (add_pos hu hv)).mpr
  nlinarith only [sq_nonneg (u * (x - t) + v * (y - t))]

private theorem adjacent_integrals_le {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {F : ℝ → ℝ} (hF : IntegrableOn F (Ioo a c)) (hF0 : ∀ x, 0 ≤ F x) :
    (∫ x in Ioo a b, F x) + (∫ x in Ioo b c, F x) ≤ ∫ x in Ioo a c, F x := by
  have hl : Ioo a b ⊆ Ioo a c := fun _ hx => ⟨hx.1, hx.2.trans hbc⟩
  have hr : Ioo b c ⊆ Ioo a c := fun _ hx => ⟨hab.trans hx.1, hx.2⟩
  have hd : Disjoint (Ioo a b) (Ioo b c) :=
    Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2.le) hy.1
  have hu : Ioo a b ∪ Ioo b c ⊆ Ioo a c := union_subset hl hr
  have h := setIntegral_mono_set (s := Ioo a b ∪ Ioo b c) (t := Ioo a c)
    hF (Eventually.of_forall hF0) (Eventually.of_forall hu)
  rw [setIntegral_union hd measurableSet_Ioo (hF.mono_set hl) (hF.mono_set hr)] at h
  exact h

/-- Merging two intervals retains the square difference of their actual means. -/
theorem intervalVariance_ge_adjacent_means {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ((b - a) * (c - b) / (c - a)) *
        (intervalMean a b f - intervalMean b c f) ^ 2 ≤ intervalVariance a c f := by
  let t := intervalMean a c f
  have hfl : MemLp f 2 (volume.restrict (Ioo a b)) := hf.mono_measure Measure.restrict_le_self
  have hfr : MemLp f 2 (volume.restrict (Ioo b c)) := hf.mono_measure Measure.restrict_le_self
  have hfi : MemLp f 2 (volume.restrict (Ioo a c)) := hf.mono_measure Measure.restrict_le_self
  have hl := integral_sub_const_sq_eq_variance hab hfl t
  have hr := integral_sub_const_sq_eq_variance hbc hfr t
  have hmeans := parallelMass_square_le (b - a) (c - b)
    (intervalMean a b f) (intervalMean b c f) t (sub_pos.mpr hab) (sub_pos.mpr hbc)
  rw [show b - a + (c - b) = c - a by ring] at hmeans
  have hsq : IntegrableOn (fun x => (f x - t) ^ 2) (Ioo a c) :=
    (hfi.sub (memLp_const t)).integrable_sq
  have hsum := adjacent_integrals_le hab hbc hsq (fun x => sq_nonneg (f x - t))
  change _ ≤ intervalVariance a c f at hsum
  linarith only [hmeans, hl, hr, hsum,
    intervalVariance_nonneg a b f, intervalVariance_nonneg b c f]

private theorem mergedPair_left_width {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((4 * a + 2 : ℕ) : ℝ) - Real.log ((4 * a : ℕ) : ℝ) = logCellWidth (2 * a) := by
  have h := haarPairWidth (show 1 ≤ 2 * a by omega)
  rw [show 2 * (2 * a) = 4 * a by omega] at h
  exact h

private theorem mergedPair_right_width {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((4 * a + 4 : ℕ) : ℝ) - Real.log ((4 * a + 2 : ℕ) : ℝ) =
      logCellWidth (2 * a + 1) := by
  have h := haarPairWidth (show 1 ≤ 2 * a + 1 by omega)
  rw [show 2 * (2 * a + 1) = 4 * a + 2 by omega,
    show 4 * a + 2 + 2 = 4 * a + 4 by omega] at h
  exact h

theorem mergedPair_width {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((4 * a + 4 : ℕ) : ℝ) - Real.log ((4 * a : ℕ) : ℝ) = logCellWidth a := by
  rw [← adjacent_logCellWidths ha, ← mergedPair_left_width ha, ← mergedPair_right_width ha]
  ring

/-- The original complete profile retains the adjacent coarse difference in its merged variance. -/
theorem completePair_merged_variance_ge (q d : ℕ → ℝ) {a X : ℕ}
    (ha : 1 ≤ a) (haX : 2 * a + 1 ≤ X) :
    haarMass a * (q (2 * a) - q (2 * a + 1)) ^ 2 ≤
      intervalVariance (Real.log ((4 * a : ℕ) : ℝ)) (Real.log ((4 * a + 4 : ℕ) : ℝ))
        (completePairProfile q d X) := by
  have hal : 1 ≤ 2 * a := by omega
  have har : 1 ≤ 2 * a + 1 := by omega
  have hab : Real.log ((4 * a : ℕ) : ℝ) < Real.log ((4 * a + 2 : ℕ) : ℝ) := by
    apply sub_pos.mp
    rw [mergedPair_left_width ha]
    exact logCellWidth_pos hal
  have hbc : Real.log ((4 * a + 2 : ℕ) : ℝ) < Real.log ((4 * a + 4 : ℕ) : ℝ) := by
    apply sub_pos.mp
    rw [mergedPair_right_width ha]
    exact logCellWidth_pos har
  have hl := intervalMean_completePairProfile q d hal (show 2 * a ≤ X by omega)
  rw [show 2 * (2 * a) = 4 * a by omega] at hl
  have hr := intervalMean_completePairProfile q d har haX
  rw [show 2 * (2 * a + 1) = 4 * a + 2 by omega,
    show 4 * a + 2 + 2 = 4 * a + 4 by omega] at hr
  have h := intervalVariance_ge_adjacent_means hab hbc
    (memLp_compact_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X))
  rw [hl, hr, mergedPair_left_width ha, mergedPair_right_width ha, mergedPair_width ha,
    ← adjacent_logCellWidths ha] at h
  exact h

/-- Disjoint merged pairs charge coarse differences with their full logarithmic weight. -/
theorem completePair_gamma_ge_log_coarseVariation (q d : ℕ → ℝ) {Y X : ℕ}
    (hYX : 2 * Y + 1 ≤ X) :
    (∑ a ∈ Finset.Icc 1 Y, Real.log (a : ℝ) * haarMass a *
      (q (2 * a) - q (2 * a + 1)) ^ 2) ≤ levyEnergy (completePairProfile q d X) := by
  let S := Finset.Icc 1 Y
  let L : S → ℝ := fun i => Real.log ((4 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((4 * (i : ℕ) + 4 : ℕ) : ℝ)
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hwidth (i : S) : U i - L i = logCellWidth (i : ℕ) := mergedPair_width (hpos i)
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
      exact_mod_cast (show 4 * (i : ℕ) + 4 ≤ 4 * (j : ℕ) by omega)
    · right
      apply Real.log_le_log (by have := hpos j; positivity)
      exact_mod_cast (show 4 * (j : ℕ) + 4 ≤ 4 * (i : ℕ) by omega)
  have h := levyEnergy_ge_sum_log_variance L U (fun i => sub_pos.mp (hw0 i)) hwidth1 hsep
    (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  apply le_trans ?_ h
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_le_sum
  intro i _hi
  have hiX : 2 * (i : ℕ) + 1 ≤ X := by have := (Finset.mem_Icc.mp i.property).2; omega
  have hlog : Real.log ((i : ℕ) : ℝ) ≤ Real.log (1 / (U i - L i)) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))
    apply (le_div_iff₀ (hw0 i)).mpr
    rw [hwidth]
    have hle := mul_le_mul_of_nonneg_left (logCellWidth_le_inv (hpos i))
      (Nat.cast_nonneg (i : ℕ))
    have hi0 : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show (i : ℕ) ≠ 0 by have := hpos i; omega)
    simpa only [mul_one_div_cancel hi0] using hle
  have hv := completePair_merged_variance_ge q d (hpos i) hiX
  have hlog0 : 0 ≤ Real.log ((i : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hpos i)
  calc
    _ = Real.log ((i : ℕ) : ℝ) * (haarMass (i : ℕ) *
        (q (2 * (i : ℕ)) - q (2 * (i : ℕ) + 1)) ^ 2) := by ring
    _ ≤ Real.log ((i : ℕ) : ℝ) * intervalVariance (L i) (U i) (completePairProfile q d X) :=
      mul_le_mul_of_nonneg_left hv hlog0
    _ ≤ _ := mul_le_mul_of_nonneg_right hlog (intervalVariance_nonneg _ _ _)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.intervalVariance_ge_adjacent_means
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completePair_merged_variance_ge
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completePair_gamma_ge_log_coarseVariation
