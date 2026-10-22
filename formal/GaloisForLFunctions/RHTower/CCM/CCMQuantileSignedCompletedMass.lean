import GaloisForLFunctions.RHTower.CCM.CCMQuantileDisplacementMass
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadCoherentQuantileGammaProducer
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadSignedCompletedErrorGammaProducer

/-!
# Exact signed mass after adjoining the terminal cell

The terminal orientation is retained before bulk and terminal are added.
This scalar density is not the vector-valued coherent field: translations
of the test vector still carry distinct phases in that field.
-/

open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace RHTower

def ccmActualHeadQuantileCompletedDisplacementDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmOutgoingQuantileDisplacementDensity N r +
    ccmActualHeadQuantileTerminalDisplacementDensity T N r

theorem integrable_ccmActualHeadQuantileTerminalDisplacementDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmActualHeadQuantileTerminalDisplacementDensity T N) := by
  have hc : Continuous (fun s : ℝ => Real.exp ((s + T) / 2)) := by fun_prop
  unfold ccmActualHeadQuantileTerminalDisplacementDensity
  dsimp only
  split_ifs
  · exact (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator
      measurableSet_Ioc
  · exact ((hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator
      measurableSet_Ioc).neg

theorem integral_ccmActualHeadQuantileTerminalDisplacementDensity (T : ℝ) (N : ℕ) :
    (∫ r : ℝ, ccmActualHeadQuantileTerminalDisplacementDensity T N r) =
      2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  have hshift := intervalIntegral.integral_comp_add_right
    (fun h : ℝ => Real.exp (h / 2)) T (a := b - T) (b := 0)
  simp only [sub_add_cancel, zero_add] at hshift
  unfold ccmActualHeadQuantileTerminalDisplacementDensity
  dsimp only
  by_cases hb : ccmOutgoingPrimeQuantileBoundary N ≤ T
  · simp_rw [if_pos hb]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (sub_nonpos.mpr hb)]
    exact hshift.trans (integral_exp_half_quantileBoundary_to_eq_massMismatch T N)
  · simp_rw [if_neg hb]
    rw [integral_neg, integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (sub_nonneg.mpr (le_of_not_ge hb)),
      ← intervalIntegral.integral_symm]
    exact hshift.trans (integral_exp_half_quantileBoundary_to_eq_massMismatch T N)

theorem integrable_ccmActualHeadQuantileCompletedDisplacementDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmActualHeadQuantileCompletedDisplacementDensity T N) :=
  (integrable_ccmOutgoingQuantileDisplacementDensity N).add
    (integrable_ccmActualHeadQuantileTerminalDisplacementDensity T N)

theorem integral_ccmActualHeadQuantileCompletedDisplacementDensity (T : ℝ) (N : ℕ) :
    (∫ r : ℝ, ccmActualHeadQuantileCompletedDisplacementDensity T N r) =
      2 * Real.exp (T / 2) - 2 := by
  unfold ccmActualHeadQuantileCompletedDisplacementDensity
  rw [integral_add (integrable_ccmOutgoingQuantileDisplacementDensity N)
    (integrable_ccmActualHeadQuantileTerminalDisplacementDensity T N),
    integral_ccmOutgoingQuantileDisplacementDensity,
    integral_ccmActualHeadQuantileTerminalDisplacementDensity]
  ring

theorem abs_ccmActualHeadQuantileTerminalDisplacementDensity_le
    (T : ℝ) (N : ℕ) (r : ℝ) :
    |ccmActualHeadQuantileTerminalDisplacementDensity T N r| ≤
      Real.exp (T / 2) + (1 + ccmOutgoingPrimeCumulative N / 2) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  have hM := ccmOutgoingPrimeCumulative_nonneg N
  have he : Real.exp (b / 2) = 1 + ccmOutgoingPrimeCumulative N / 2 :=
    exp_half_ccmOutgoingPrimeQuantileBoundary N
  unfold ccmActualHeadQuantileTerminalDisplacementDensity
  dsimp only
  by_cases hb : b ≤ T
  · rw [if_pos hb]
    by_cases hr : r ∈ Ioc (b - T) 0
    · rw [indicator_of_mem hr, abs_of_pos (Real.exp_pos _)]
      have hx : Real.exp ((r + T) / 2) ≤ Real.exp (T / 2) :=
        Real.exp_le_exp.mpr (by linarith [hr.2])
      linarith
    · rw [indicator_of_notMem hr, abs_zero]
      positivity
  · rw [if_neg hb, abs_neg]
    by_cases hr : r ∈ Ioc 0 (b - T)
    · rw [indicator_of_mem hr, abs_of_pos (Real.exp_pos _)]
      have hx : Real.exp ((r + T) / 2) ≤ Real.exp (b / 2) :=
        Real.exp_le_exp.mpr (by linarith [hr.2])
      linarith [Real.exp_pos (T / 2)]
    · rw [indicator_of_notMem hr, abs_zero]
      positivity

theorem ccmOutgoingPrimeCumulative_le_twice_head (N : ℕ) :
    ccmOutgoingPrimeCumulative N ≤ 2 * (N : ℝ) := by
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => criticalMellinAtomWeight_le_two n)
  simpa only [ccmOutgoingPrimeCumulative, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_comm] using h

theorem abs_ccmActualHeadQuantileCompletedDisplacementDensity_le_height
    (T : ℝ) (N : ℕ) (r : ℝ) :
    |ccmActualHeadQuantileCompletedDisplacementDensity T N r| ≤
      ((N : ℝ) + 1) ^ 2 + Real.exp (T / 2) := by
  have hbulk := ccmOutgoingQuantileDisplacementDensity_le_height N r
  have hterminal := abs_ccmActualHeadQuantileTerminalDisplacementDensity_le T N r
  have hmass := ccmOutgoingPrimeCumulative_le_twice_head N
  have hbound := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have htri := abs_add_le (ccmOutgoingQuantileDisplacementDensity N r)
    (ccmActualHeadQuantileTerminalDisplacementDensity T N r)
  rw [abs_of_nonneg (ccmOutgoingQuantileDisplacementDensity_nonneg N r)] at htri
  unfold ccmActualHeadQuantileCompletedDisplacementDensity
  nlinarith

end RHTower
