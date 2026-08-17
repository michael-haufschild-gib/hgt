import GaloisForLFunctions.HTGeometry.PeriodicMeanZeroAveraging
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The parity square wave

The alternation of extension parity along a boundary phase is the centred indicator

`S(y) = 1_{sin y > 0} - 1/2`,

a `2π`-periodic function taking only the two values `±1/2`, whose integral over one period
vanishes: the sine is positive exactly on `(0, π)` modulo `2π`, so the two halves cancel.

That is precisely the input of the mean-zero averaging bound, so a phase whose inverse speed is
uniformly small and of small total variation averages the parity alternation to its mean.
-/

open MeasureTheory intervalIntegral Real Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The centred parity alternation. -/
def parityWave (y : ℝ) : ℝ := (if 0 < Real.sin y then (1 : ℝ) else 0) - 1 / 2

theorem parityWave_periodic : Function.Periodic parityWave (2 * Real.pi) := by
  intro y
  rw [parityWave, parityWave, Real.sin_add_two_pi]

theorem abs_parityWave_le (y : ℝ) : |parityWave y| ≤ 1 / 2 := by
  rw [parityWave]
  by_cases h : 0 < Real.sin y
  · rw [if_pos h]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 - 1/2)]
    norm_num
  · rw [if_neg h]
    rw [abs_of_nonpos (by norm_num : (0:ℝ) - 1/2 ≤ 0)]
    norm_num

theorem measurable_parityWave : Measurable parityWave := by
  have hopen : IsOpen {y : ℝ | 0 < Real.sin y} :=
    isOpen_lt continuous_const Real.continuous_sin
  have hmeas : MeasurableSet {y : ℝ | 0 < Real.sin y} := hopen.measurableSet
  have : Measurable fun y : ℝ => if 0 < Real.sin y then (1 : ℝ) else 0 :=
    Measurable.ite hmeas measurable_const measurable_const
  exact this.sub measurable_const

theorem intervalIntegrable_parityWave (a b : ℝ) :
    IntervalIntegrable parityWave volume a b := by
  have hbound : ∀ (s : Set ℝ), ∀ᵐ y ∂((volume : Measure ℝ).restrict s), ‖parityWave y‖ ≤ 1 / 2 := by
    intro s
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact abs_parityWave_le y
  constructor
  · exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      measurable_parityWave.aestronglyMeasurable (hbound _)
  · exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      measurable_parityWave.aestronglyMeasurable (hbound _)

/-- On the positive half period the wave is `+1/2`. -/
theorem parityWave_eq_half {y : ℝ} (h0 : 0 < y) (hπ : y < Real.pi) :
    parityWave y = 1 / 2 := by
  rw [parityWave, if_pos (Real.sin_pos_of_pos_of_lt_pi h0 hπ)]
  norm_num

/-- On the negative half period the wave is `-1/2`. -/
theorem parityWave_eq_neg_half {y : ℝ} (h0 : Real.pi < y) (hπ : y < 2 * Real.pi) :
    parityWave y = -(1 / 2) := by
  have hneg : Real.sin y < 0 := by
    have hpos : 0 < Real.sin (y - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hpos
    linarith
  rw [parityWave, if_neg (by linarith)]
  norm_num

/-- **The wave has zero mean over one period.** -/
theorem parityWave_mean_zero (a : ℝ) :
    ∫ y in a..(a + 2 * Real.pi), parityWave y = 0 := by
  have hshift := parityWave_periodic.intervalIntegral_add_eq a 0
  rw [hshift, zero_add]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnullπ : ∀ᵐ y : ℝ, y ≠ Real.pi := by
    rw [MeasureTheory.ae_iff]
    simp
  have hnull2π : ∀ᵐ y : ℝ, y ≠ 2 * Real.pi := by
    rw [MeasureTheory.ae_iff]
    simp
  have hfirst : ∫ y in (0 : ℝ)..Real.pi, parityWave y = ∫ y in (0 : ℝ)..Real.pi, (1 / 2 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hnullπ] with y hyne hy
    rw [Set.uIoc_of_le hπ.le] at hy
    exact parityWave_eq_half hy.1 (lt_of_le_of_ne hy.2 hyne)
  have hsecond : ∫ y in Real.pi..(2 * Real.pi), parityWave y
      = ∫ y in Real.pi..(2 * Real.pi), (-(1 / 2) : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hnull2π] with y hyne hy
    rw [Set.uIoc_of_le (by linarith : Real.pi ≤ 2 * Real.pi)] at hy
    exact parityWave_eq_neg_half hy.1 (lt_of_le_of_ne hy.2 hyne)
  have hsplit : (∫ y in (0 : ℝ)..Real.pi, parityWave y)
      + (∫ y in Real.pi..(2 * Real.pi), parityWave y)
      = ∫ y in (0 : ℝ)..(2 * Real.pi), parityWave y :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_parityWave _ _) (intervalIntegrable_parityWave _ _)
  rw [← hsplit, hfirst, hsecond]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  ring

end GaloisForLFunctions.HTGeometry
