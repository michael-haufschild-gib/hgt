import GaloisForLFunctions.RHTower.CCM.CCMActualHeadQuantileGammaChiSquareProducer
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Mass and height of the actual displaced prime cells

Displacing cells does not change their von-Mangoldt masses. Their complete
sum has an explicit height bound in terms of its own mass; overlaps are
retained. Chebyshev's unconditional lower bound applies to the same sum.
-/

open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
namespace RHTower

theorem integrable_ccmOutgoingQuantileDisplacementCellDensity (n : ℕ) :
    Integrable (ccmOutgoingQuantileDisplacementCellDensity n) := by
  have hc : Continuous (fun r : ℝ => Real.exp ((r + Real.log n) / 2)) := by fun_prop
  exact (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

theorem integral_ccmOutgoingQuantileDisplacementCellDensity (n : ℕ) :
    (∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r) =
      criticalMellinAtomWeight n := by
  have hm := ccmOutgoingPrimeQuantileBoundary_mono_step n
  unfold ccmOutgoingQuantileDisplacementCellDensity
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (sub_le_sub_right hm (Real.log n))]
  have hs := intervalIntegral.integral_comp_add_right
    (fun h : ℝ => Real.exp (h / 2)) (Real.log n)
    (a := ccmOutgoingPrimeQuantileBoundary n - Real.log n)
    (b := ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)
  simpa only [sub_add_cancel, integral_exp_half_quantileCell_eq_atomWeight] using hs

theorem integrable_ccmOutgoingQuantileDisplacementDensity (N : ℕ) :
    Integrable (ccmOutgoingQuantileDisplacementDensity N) := by
  exact integrable_finsetSum _ fun n _ => integrable_ccmOutgoingQuantileDisplacementCellDensity n

theorem integral_ccmOutgoingQuantileDisplacementDensity (N : ℕ) :
    (∫ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r) =
      ccmOutgoingPrimeCumulative N := by
  unfold ccmOutgoingQuantileDisplacementDensity ccmOutgoingPrimeCumulative
  rw [integral_finsetSum _ fun n _ => integrable_ccmOutgoingQuantileDisplacementCellDensity n]
  simp_rw [integral_ccmOutgoingQuantileDisplacementCellDensity]

theorem ccmOutgoingQuantileDisplacementDensity_le_height (N : ℕ) (r : ℝ) :
    ccmOutgoingQuantileDisplacementDensity N r ≤
      (N : ℝ) * (1 + ccmOutgoingPrimeCumulative N / 2) := by
  have hm : Monotone ccmOutgoingPrimeQuantileBoundary :=
    monotone_nat_of_le_succ ccmOutgoingPrimeQuantileBoundary_mono_step
  have hterm (n : ℕ) (hn : n ∈ Finset.range N) :
      ccmOutgoingQuantileDisplacementCellDensity n r ≤
        Real.exp (ccmOutgoingPrimeQuantileBoundary N / 2) := by
    unfold ccmOutgoingQuantileDisplacementCellDensity
    by_cases hr : r ∈ Ioc
        (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
        (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)
    · rw [indicator_of_mem hr]
      apply Real.exp_le_exp.mpr
      have hb := hm (Nat.succ_le_of_lt (Finset.mem_range.mp hn))
      linarith [hr.2]
    · rw [indicator_of_notMem hr]
      positivity
  have hs := Finset.sum_le_sum hterm
  simpa only [ccmOutgoingQuantileDisplacementDensity, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, exp_half_ccmOutgoingPrimeQuantileBoundary] using hs

theorem ccmOutgoingPrimeCumulative_succ_eq_primeMassHalf (N : ℕ) :
    ccmOutgoingPrimeCumulative (N + 1) = primeMassHalf (N : ℝ) := by
  unfold ccmOutgoingPrimeCumulative primeMassHalf
  rw [Nat.floor_natCast]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  · intro n _
    exact criticalMellinAtomWeight_eq_div_sqrt n

theorem eventually_sqrt_le_ccmOutgoingPrimeCumulative :
    ∀ᶠ N : ℕ in atTop,
      (Real.log 2 / 2) * Real.sqrt (N : ℝ) ≤ ccmOutgoingPrimeCumulative (N + 1) := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually eventually_sqrt_le_primeMassHalf
  simpa only [← ccmOutgoingPrimeCumulative_succ_eq_primeMassHalf] using h

end RHTower
