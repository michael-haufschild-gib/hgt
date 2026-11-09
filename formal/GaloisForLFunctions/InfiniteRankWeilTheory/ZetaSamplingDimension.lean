import GaloisForLFunctions.InfiniteRankWeilTheory.IsolatedTopSamplingDimension
import GaloisForLFunctions.InfiniteRankWeilTheory.ZetaMetricTopDetection
import GaloisForLFunctions.RHTower.WeilLagFunctionExponentialExceptionCriterion

/-!
# Positive-dimensional recurrence and the zeta abscissa law

Failure of AAL makes the bases with recurrent sub-top Weil-lag readings zero-dimensional.
Thus positive Hausdorff dimension of the recurrent-base set at every positive rate forces
AAL. Together with zeros approaching the critical line, this is equivalent to RH.
-/

open Complex Set Filter MeasureTheory MeasureTheory.Measure
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- At and above the global zero exponent, every positive base has the required recurrence
bound at every level. -/
theorem lagRecurrenceBases_eq_Ioi_of_abscissa_le {a : ℝ}
    (ha : RHTower.zetaZeroAbscissa - 1 / 2 ≤ a) : lagRecurrenceBases a = Ioi 0 := by
  apply Set.Subset.antisymm
  · intro ℓ hℓ
    exact hℓ.1
  · intro ℓ hℓ
    have hq : ∀ q : RHTower.XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + a := by
      intro q
      have h := RHTower.re_le_zetaZeroAbscissa (RHTower.riemannZeta_eq_zero_of_xiZeroCopy q)
      linarith only [h, ha]
    refine ⟨hℓ, RHTower.lagWeightTotal, Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun n => ?_)⟩
    have hbound := RHTower.abs_weilLagFunctionReal_le_of_strip hq
      (L := (n : ℝ) * ℓ) (mul_nonneg (Nat.cast_nonneg _) hℓ.le)
    simpa only [RHTower.weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
      mul_assoc, mul_comm, mul_left_comm] using hbound

/-- The recurrent-base set has full real dimension at every rate at or above the global top. -/
theorem dimH_lagRecurrenceBases_eq_one_of_abscissa_le {a : ℝ}
    (ha : RHTower.zetaZeroAbscissa - 1 / 2 ≤ a) : dimH (lagRecurrenceBases a) = 1 := by
  rw [lagRecurrenceBases_eq_Ioi_of_abscissa_le ha]
  simpa only [Module.finrank_self, Nat.cast_one] using
    (Real.dimH_of_mem_nhds (x := (1 : ℝ)) (s := Ioi 0)
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)))

/-- Under failure of actual zeta AAL, one dimension-zero set contains all sub-top recurrence
bases, simultaneously over all rates and constants. -/
theorem dimH_all_subtop_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    dimH {ℓ : ℝ | ∃ a : ℝ, a < RHTower.zetaZeroAbscissa - 1 / 2 ∧
      ℓ ∈ lagRecurrenceBases a} = 0 := by
  classical
  rw [asymptoticAbscissaLaw_zetaConfig_iff,
    not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨F, Θ, Θ₂, hFne, hΘ, hgap, hF, hrest⟩ := hnot
  have hΘeq : Θ = RHTower.zetaZeroAbscissa := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := hFne
      rw [← hF j hj]
      exact RHTower.re_le_zetaZeroAbscissa (RHTower.riemannZeta_eq_zero_of_xiZeroCopy j)
    · apply ZeroConfigurationGeometry.zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le hΘ.le
      intro j
      by_cases hj : j ∈ F
      · exact (hF j hj).le
      · exact (hrest j hj).trans hgap.le
  have hvis : ∃ j ∈ F,
      (∑ i ∈ F with (zetaConfig i).im = (zetaConfig j).im, lagWeight i) ≠ 0 := by
    obtain ⟨j, hj⟩ := hFne
    refine ⟨j, hj, fun h => ?_⟩
    have hre := congrArg Complex.re h
    rw [Complex.re_sum, Complex.zero_re] at hre
    have hpos : 0 < ∑ i ∈ F with (zetaConfig i).im = (zetaConfig j).im,
        (lagWeight i).re := Finset.sum_pos (fun i _ => re_lagWeight_pos i)
          ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩⟩
    linarith only [hre, hpos]
  have hdim := dimH_all_subtop_towerRecurrenceBases_eq_zero
    zetaConfig lagWeight summable_norm_lagWeight F hgap hF hrest hvis
  rw [hΘeq] at hdim
  simpa only [towerRecurrenceBases, lagRecurrenceBases, weilLagFunction_mul_eq_levelSum] using hdim

/-- At every sub-top rate, recurrent Weil-lag readings occur only on a zero-dimensional set
of positive bases. -/
theorem dimH_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) {a : ℝ}
    (ha : a < RHTower.zetaZeroAbscissa - 1 / 2) : dimH (lagRecurrenceBases a) = 0 := by
  have hsub : lagRecurrenceBases a ⊆ {ℓ : ℝ | ∃ q : ℝ,
      q < RHTower.zetaZeroAbscissa - 1 / 2 ∧ ℓ ∈ lagRecurrenceBases q} :=
    fun _ hℓ => ⟨a, ha, hℓ⟩
  exact le_antisymm ((dimH_mono hsub).trans_eq
    (dimH_all_subtop_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw hnot)) bot_le

/-- When AAL fails, recurrence-base dimension has a sharp jump at the global top exponent. -/
theorem dimH_lagRecurrenceBases_eq_ite_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) (a : ℝ) :
    dimH (lagRecurrenceBases a) = if a < RHTower.zetaZeroAbscissa - 1 / 2 then 0 else 1 := by
  by_cases ha : a < RHTower.zetaZeroAbscissa - 1 / 2
  · rw [if_pos ha]
    exact dimH_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw hnot ha
  · rw [if_neg ha]
    exact dimH_lagRecurrenceBases_eq_one_of_abscissa_le (le_of_not_gt ha)

/-- Recurrence on a positive-dimensional family at each positive rate excludes every finite
exceptional top, even if the families are singular for Lebesgue measure and vary with the rate. -/
theorem asymptoticAbscissaLaw_of_forall_pos_dimH_lagRecurrenceBases
    (hpos : ∀ a : ℝ, 0 < a → 0 < dimH (lagRecurrenceBases a)) :
    RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  have hΘ := (not_asymptoticAbscissaLaw_implies_metric_top_detection hnot).1
  have ha : 0 < (RHTower.zetaZeroAbscissa - 1 / 2) / 2 := by linarith only [hΘ]
  exact (ne_of_gt (hpos _ ha))
    (dimH_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw hnot
      (a := (RHTower.zetaZeroAbscissa - 1 / 2) / 2) (by linarith only [hΘ]))

/-- RH is zeros approaching the line plus positive Hausdorff dimension of the bases with
recurrent lag bounds at every positive rate. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_positive_dimensional_recurrence :
    RiemannHypothesis ↔ RHTower.BacklundConverse.ZerosApproachLine ∧
      ∀ a : ℝ, 0 < a → 0 < dimH (lagRecurrenceBases a) := by
  constructor
  · intro hRH
    obtain ⟨hZ, hpos⟩ :=
      riemannHypothesis_iff_zerosApproachLine_and_metric_recurrence_at_each_rate.mp hRH
    refine ⟨hZ, fun a ha => ?_⟩
    have hH : (hausdorffMeasure (1 : ℝ)) (lagRecurrenceBases a) ≠ 0 := by
      rw [hausdorffMeasure_real]
      exact (hpos a ha).ne'
    have hd : (1 : ENNReal) ≤ dimH (lagRecurrenceBases a) :=
      le_dimH_of_hausdorffMeasure_ne_zero (d := (1 : NNReal)) hH
    exact (by norm_num : (0 : ENNReal) < 1).trans_le hd
  · rintro ⟨hZ, hpos⟩
    exact RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZ, asymptoticAbscissaLaw_of_forall_pos_dimH_lagRecurrenceBases hpos⟩

#print axioms dimH_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw
#print axioms dimH_all_subtop_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw
#print axioms dimH_lagRecurrenceBases_eq_ite_of_not_asymptoticAbscissaLaw
#print axioms riemannHypothesis_iff_zerosApproachLine_and_positive_dimensional_recurrence

end GaloisForLFunctions.InfiniteRankWeilTheory
