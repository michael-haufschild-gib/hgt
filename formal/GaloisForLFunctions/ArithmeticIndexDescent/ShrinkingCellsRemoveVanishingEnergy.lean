import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceKernelEnergyBoundsTheSchurCost
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shrinking a fixed arithmetic pattern removes vanishing energy

The union of `N` logarithmic cells has measure at most `N w`. For a fixed probe
the source kernel is bounded on a common compact window for all `0 ≤ w ≤ 1`.
Its square energy, and hence the entire completed section removal, is `O(w)`.
This is uniform over all profile families at fixed `N`, but not over growing `N`.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

/-- The exact cells occupy at most their summed lengths; overlap only lowers this bound. -/
theorem measureReal_arithmeticSectionSupport_le (N : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    volume.real (arithmeticSectionSupport N w) ≤ (N : ℝ) * w := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        volume.real (Set.Icc (Real.log n) (Real.log n + w)) :=
      measureReal_biUnion_finset_le (μ := volume) (Finset.Icc 1 N)
        (fun n => Set.Icc (Real.log n) (Real.log n + w))
    _ = _ := by
      simp only [Real.volume_real_Icc, add_sub_cancel_left, max_eq_left hw,
        Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- All widths at most one share a common source window. -/
theorem arithmeticSectionSupport_subset_fixed_window (N : ℕ) {w : ℝ} (hw : w ≤ 1) :
    arithmeticSectionSupport N w ⊆ Set.Icc 0 (Real.log N + 1) := by
  intro u hu
  simp only [arithmeticSectionSupport, Set.mem_iUnion] at hu
  obtain ⟨n, hn, hu⟩ := hu
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hlog0 := Real.log_natCast_nonneg n
  have hlogN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  exact ⟨hlog0.trans hu.1, by linarith only [hu.2, hlogN, hw]⟩

/-- Kernel energy on a fixed arithmetic pattern is bounded linearly in its cell width. -/
theorem exists_sourceKernelEnergy_le_mul_width (N : ℕ) (g : realTests) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      sourceKernelEnergy (arithmeticSectionSupport N w) g ≤ B * w := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 (Real.log N + 1))).exists_bound_of_continuousOn
    (continuous_weilSourceKernel g).continuousOn
  refine ⟨N * (max C 0) ^ 2, mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _), ?_⟩
  intro w hw0 hw1
  have hs := isCompact_arithmeticSectionSupport N w
  have hbound (u : ℝ) (hu : u ∈ arithmeticSectionSupport N w) :
      ‖weilSourceKernel g u‖ ^ 2 ≤ (max C 0) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      ((hC u (arithmeticSectionSupport_subset_fixed_window N hw1 hu)).trans (le_max_left C 0)) 2
  calc
    sourceKernelEnergy (arithmeticSectionSupport N w) g ≤
        ∫ _u in arithmeticSectionSupport N w, (max C 0) ^ 2 :=
      setIntegral_mono_on (integrableOn_sourceKernel_sq hs g)
        (ContinuousOn.integrableOn_compact hs continuousOn_const) hs.measurableSet hbound
    _ = volume.real (arithmeticSectionSupport N w) * (max C 0) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ ((N : ℝ) * w) * (max C 0) ^ 2 :=
      mul_le_mul_of_nonneg_right (measureReal_arithmeticSectionSupport_le N hw0) (sq_nonneg _)
    _ = _ := by ring

/-- Every finite profile family and the entire source completion obey one shrinking-width bound. -/
theorem exists_sectionCompletionEnergy_le_mul_width {N : ℕ} (hN : 1 ≤ N) (g : realTests) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w : ℝ) (hw0 : 0 < w)
      (hw : w ≤ fullSectionRatio * atomSpacing N), w ≤ 1 →
        sectionCompletionEnergy hN hw0 hw g ≤ B * w := by
  obtain ⟨B, hB, hb⟩ := exists_sourceKernelEnergy_le_mul_width N g
  exact ⟨B, hB, fun w hw0 hw hw1 =>
    (sectionCompletionEnergy_le_sourceKernelEnergy hN hw0 hw g).trans (hb w hw0.le hw1)⟩

/-- At fixed `N`, arbitrarily narrow cells remove arbitrarily little completed energy. -/
theorem sectionCompletionEnergy_vanishes_with_width {N : ℕ} (hN : 1 ≤ N) (g : realTests)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (w : ℝ) (hw0 : 0 < w)
      (hw : w ≤ fullSectionRatio * atomSpacing N), w < δ →
        sectionCompletionEnergy hN hw0 hw g < ε := by
  obtain ⟨B, hB, hb⟩ := exists_sectionCompletionEnergy_le_mul_width hN g
  have hB1 : 0 < B + 1 := by linarith only [hB]
  refine ⟨min 1 (ε / (B + 1)), lt_min zero_lt_one (div_pos hε hB1), ?_⟩
  intro w hw0 hw hδ
  have hw1 : w ≤ 1 := (hδ.trans_le (min_le_left _ _)).le
  have hsmall : w * (B + 1) < ε :=
    (lt_div_iff₀ hB1).mp (hδ.trans_le (min_le_right _ _))
  have hbound := hb w hw0 hw hw1
  nlinarith only [hbound, hsmall, hw0]

/-- Shrinking a fixed pattern returns the residual to the original signed diagonal. -/
theorem completedSectionResidualForm_returns_to_original {N : ℕ} (hN : 1 ≤ N)
    (g : realTests) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (w : ℝ) (hw0 : 0 < w)
      (hw : w ≤ fullSectionRatio * atomSpacing N), w < δ →
        realWeilForm g g - ε < completedSectionResidualForm hN hw0 hw g g ∧
          completedSectionResidualForm hN hw0 hw g g ≤ realWeilForm g g := by
  obtain ⟨δ, hδ, hb⟩ := sectionCompletionEnergy_vanishes_with_width hN g hε
  refine ⟨δ, hδ, ?_⟩
  intro w hw0 hw hwδ
  refine ⟨?_, completedSectionResidualForm_self_le hN hw0 hw g⟩
  change realWeilForm g g - ε < realWeilForm g g - sectionCompletionPair hN hw0 hw g g
  rw [sectionCompletionPair_self]
  exact sub_lt_sub_left (hb w hw0 hw hwδ) _

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_sourceKernelEnergy_le_mul_width
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sectionCompletionEnergy_vanishes_with_width
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completedSectionResidualForm_returns_to_original
