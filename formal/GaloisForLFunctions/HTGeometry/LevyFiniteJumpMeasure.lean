import GaloisForLFunctions.HTGeometry.LevyLaplaceTruncation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-! Each positive cutoff gives a genuine finite positive jump measure. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
noncomputable section
namespace GaloisForLFunctions.HTGeometry

def levyFiniteJumpWeight (n : ℕ) (h : ℝ≥0) : ℝ≥0 :=
  if levyJumpCutoff n ≤ h then (1 + h) / h else 0

theorem measurable_levyFiniteJumpWeight (n : ℕ) : Measurable (levyFiniteJumpWeight n) := by
  unfold levyFiniteJumpWeight
  apply Measurable.ite measurableSet_Ici _ measurable_const
  fun_prop

theorem levyFiniteJumpWeight_le (n : ℕ) (h : ℝ≥0) :
    levyFiniteJumpWeight n h ≤ 1 + 1 / levyJumpCutoff n := by
  by_cases hh : levyJumpCutoff n ≤ h
  · have hpos : 0 < h := (levyJumpCutoff_pos n).trans_le hh
    simp only [levyFiniteJumpWeight, if_pos hh, add_div, div_self hpos.ne', add_comm]
    exact add_le_add_right (one_div_le_one_div_of_le (levyJumpCutoff_pos n) hh) 1
  · simp only [levyFiniteJumpWeight, if_neg hh]
    positivity

def levyFiniteJumpMeasure (η : Measure ℝ≥0) (n : ℕ) : Measure ℝ≥0 :=
  η.withDensity (fun h => (levyFiniteJumpWeight n h : ℝ≥0∞))

variable (η : Measure ℝ≥0) [IsFiniteMeasure η]

theorem integrable_levyFiniteJumpWeight (n : ℕ) :
    Integrable (fun h => (levyFiniteJumpWeight n h : ℝ)) η := by
  refine (integrable_const ((1 + 1 / levyJumpCutoff n : ℝ≥0) : ℝ)).mono'
    (measurable_levyFiniteJumpWeight n).coe_nnreal_real.aestronglyMeasurable ?_
  refine Eventually.of_forall fun h => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (levyFiniteJumpWeight n h).coe_nonneg]
  exact_mod_cast levyFiniteJumpWeight_le n h

instance (n : ℕ) : IsFiniteMeasure (levyFiniteJumpMeasure η n) := by
  apply isFiniteMeasure_withDensity
  rw [lintegral_coe_eq_integral _ (integrable_levyFiniteJumpWeight η n)]
  exact ENNReal.ofReal_ne_top

omit [IsFiniteMeasure η] in
theorem levyFiniteJumpMeasure_zero_atom (hη : η {0} = 0) (n : ℕ) :
    levyFiniteJumpMeasure η n {0} = 0 :=
  withDensity_absolutelyContinuous η _ hη

omit [IsFiniteMeasure η] in
theorem integral_levyFiniteJumpMeasure (n : ℕ) (z : ℂ) :
    (∫ h : ℝ≥0, 1 - Complex.exp (-z * ((h : ℝ) : ℂ)) ∂levyFiniteJumpMeasure η n) =
      levyLaplaceJump (levyLargeControl η n) z := by
  rw [levyFiniteJumpMeasure,
    integral_withDensity_eq_integral_smul (measurable_levyFiniteJumpWeight n),
    levyLaplaceJump, levyLargeControl, ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  refine Eventually.of_forall fun h => ?_
  by_cases hh : levyJumpCutoff n ≤ h
  · have hne : h ≠ 0 := ne_of_gt ((levyJumpCutoff_pos n).trans_le hh)
    rw [Set.indicator_of_mem (s := Ici (levyJumpCutoff n)) hh]
    simp only [levyFiniteJumpWeight, if_pos hh, levyLaplaceKernel, if_neg hne,
      NNReal.smul_def, Complex.real_smul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_one]
  · rw [Set.indicator_of_notMem (s := Ici (levyJumpCutoff n)) hh]
    simp only [levyFiniteJumpWeight, if_neg hh, zero_smul]

end GaloisForLFunctions.HTGeometry
