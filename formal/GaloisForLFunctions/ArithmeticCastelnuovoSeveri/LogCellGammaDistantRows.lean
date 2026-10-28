import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCellGammaRowGeometry
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaPairRemainder

/-!
# Finite distant Gamma rows

Distinct logarithmic cells have disjoint interiors. Their integrated far row
is bounded by two fixed Gamma tails, independently of the finite upper horizon.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry MeanZeroIntervals

/-- The actual distant interactions have one uniform two-tail bound, at every finite horizon. -/
theorem gamma_logCell_distant_sum_le {a : ℕ} (ha : 1 ≤ a) (s : ℝ) (S : Finset ℕ)
    (hS : ∀ b ∈ S, 1 ≤ b ∧ (2 * b < a ∨ 2 * a < b)) :
    (∑ b ∈ S, gammaIntervalKernel (s + Real.log (a : ℝ))
      (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log (b : ℝ))
      (s + Real.log ((b + 1 : ℕ) : ℝ))) ≤
      ENNReal.ofReal (2 * logCellWidth a * gammaTailMass (Real.log (3 / 2 : ℝ))) := by
  classical
  let I : ℕ → Set ℝ := fun b => Ioo (s + Real.log (b : ℝ))
    (s + Real.log ((b + 1 : ℕ) : ℝ))
  let δ : ℝ := Real.log (3 / 2 : ℝ)
  let F := Iio (s + Real.log (a : ℝ) - δ) ∪
    Ioi (s + Real.log ((a + 1 : ℕ) : ℝ) + δ)
  have hIm (i : S) : MeasurableSet (I i) := measurableSet_Ioo
  have hpd : Pairwise (Function.onFun Disjoint (fun i : S => I i)) := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Subtype.ext he)
    apply disjoint_left.mpr
    intro y hyi hyj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlog : Real.log (((i : ℕ) + 1 : ℕ) : ℝ) ≤ Real.log ((j : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show (i : ℕ) + 1 ≤ j by omega))
      change s + Real.log ((i : ℕ) : ℝ) < y ∧ y < s + Real.log (((i : ℕ) + 1 : ℕ) : ℝ) at hyi
      change s + Real.log ((j : ℕ) : ℝ) < y ∧ y < s + Real.log (((j : ℕ) + 1 : ℕ) : ℝ) at hyj
      linarith only [hyi.2, hyj.1, hlog]
    · have hlog : Real.log (((j : ℕ) + 1 : ℕ) : ℝ) ≤ Real.log ((i : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show (j : ℕ) + 1 ≤ i by omega))
      change s + Real.log ((i : ℕ) : ℝ) < y ∧ y < s + Real.log (((i : ℕ) + 1 : ℕ) : ℝ) at hyi
      change s + Real.log ((j : ℕ) : ℝ) < y ∧ y < s + Real.log (((j : ℕ) + 1 : ℕ) : ℝ) at hyj
      linarith only [hyj.2, hyi.1, hlog]
  have hsub : (⋃ i : S, I i) ⊆ F := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hbase : y - s ∈ Ioo (Real.log ((i : ℕ) : ℝ))
        (Real.log (((i : ℕ) + 1 : ℕ) : ℝ)) := by
      change s + Real.log ((i : ℕ) : ℝ) < y ∧ y < s + Real.log (((i : ℕ) + 1 : ℕ) : ℝ) at hi
      constructor <;> linarith only [hi.1, hi.2]
    have h := logCell_distant_subset ha (hS i i.property).1 (hS i i.property).2 hbase
    rcases h with hl | hr
    · left
      change y < s + Real.log (a : ℝ) - δ
      change y - s < Real.log (a : ℝ) - δ at hl
      linarith only [hl]
    · right
      change s + Real.log ((a + 1 : ℕ) : ℝ) + δ < y
      change Real.log ((a + 1 : ℕ) : ℝ) + δ < y - s at hr
      linarith only [hr]
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (archLevyDensity |p.2 - p.1|)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_archLevyDensity.comp (measurable_snd.sub measurable_fst).abs)
  have hinner (x : ℝ) :
      (∑ i : S, ∫⁻ y in I i, ENNReal.ofReal (archLevyDensity |y - x|)) =
        ∫⁻ y in ⋃ i : S, I i, ENNReal.ofReal (archLevyDensity |y - x|) := by
    rw [lintegral_iUnion hIm hpd, tsum_fintype]
  have hwidth : (s + Real.log ((a + 1 : ℕ) : ℝ)) - (s + Real.log (a : ℝ)) =
      logCellWidth a := by simp only [add_sub_add_left_eq_sub, logCellWidth, Nat.cast_add, Nat.cast_one]
  have hab : s + Real.log (a : ℝ) < s + Real.log ((a + 1 : ℕ) : ℝ) := by
    apply sub_pos.mp
    rw [hwidth]
    exact logCellWidth_pos ha
  calc
    _ = ∑ i : S, ∫⁻ x in I a, ∫⁻ y in I i, ENNReal.ofReal (archLevyDensity |y - x|) := by
      exact (Finset.sum_coe_sort S (fun b : ℕ =>
        ∫⁻ x in I a, ∫⁻ y in I b, ENNReal.ofReal (archLevyDensity |y - x|))).symm
    _ = ∫⁻ x in I a, ∑ i : S, ∫⁻ y in I i, ENNReal.ofReal (archLevyDensity |y - x|) := by
      rw [lintegral_finsetSum _ fun _ _ => hm.lintegral_prod_right']
    _ = ∫⁻ x in I a, ∫⁻ y in ⋃ i : S, I i, ENNReal.ofReal (archLevyDensity |y - x|) :=
      lintegral_congr hinner
    _ ≤ ∫⁻ x in I a, ∫⁻ y in F, ENNReal.ofReal (archLevyDensity |y - x|) :=
      lintegral_mono fun _ => lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ ≤ _ := by
      have h := gamma_separated_interval_rows_le
        (show 0 < δ from Real.log_pos (by norm_num)) hab
        (show (s + Real.log (a : ℝ) - δ) + δ ≤ s + Real.log (a : ℝ) by linarith only [])
        (show s + Real.log ((a + 1 : ℕ) : ℝ) + δ ≤ s + Real.log ((a + 1 : ℕ) : ℝ) + δ from le_rfl)
      rw [hwidth] at h
      exact h

#print axioms gamma_logCell_distant_sum_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
