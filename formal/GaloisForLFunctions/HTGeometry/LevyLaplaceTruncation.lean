import GaloisForLFunctions.HTGeometry.LevyLaplaceExponent
import Mathlib.Analysis.SpecificLimits.Basic

/-! Small-jump tails vanish while preserving accretivity. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal
noncomputable section
namespace GaloisForLFunctions.HTGeometry

def levyJumpCutoff (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)

theorem levyJumpCutoff_pos (n : ℕ) : 0 < levyJumpCutoff n := by
  unfold levyJumpCutoff
  positivity

theorem tendsto_levyJumpCutoff_zero : Tendsto levyJumpCutoff atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def levySmallControl (η : Measure ℝ≥0) (n : ℕ) : Measure ℝ≥0 :=
  η.restrict (Iio (levyJumpCutoff n))

def levyLargeControl (η : Measure ℝ≥0) (n : ℕ) : Measure ℝ≥0 :=
  η.restrict (Ici (levyJumpCutoff n))

instance (η : Measure ℝ≥0) [IsFiniteMeasure η] (n : ℕ) :
    IsFiniteMeasure (levySmallControl η n) := by
  unfold levySmallControl
  infer_instance

instance (η : Measure ℝ≥0) [IsFiniteMeasure η] (n : ℕ) :
    IsFiniteMeasure (levyLargeControl η n) := by
  unfold levyLargeControl
  infer_instance

theorem levySmallControl_add_large (η : Measure ℝ≥0) (n : ℕ) :
    levySmallControl η n + levyLargeControl η n = η := by
  simpa only [levySmallControl, levyLargeControl, compl_Iio] using
    (Measure.restrict_add_restrict_compl (μ := η)
      (measurableSet_Iio (a := levyJumpCutoff n)))

variable (η : Measure ℝ≥0) [IsFiniteMeasure η]

theorem levyLaplaceJump_split {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    levyLaplaceJump η z = levyLaplaceJump (levySmallControl η n) z +
      levyLaplaceJump (levyLargeControl η n) z := by
  calc
    levyLaplaceJump η z =
        levyLaplaceJump (levySmallControl η n + levyLargeControl η n) z :=
      congrArg (fun μ => levyLaplaceJump μ z) (levySmallControl_add_large η n).symm
    _ = _ := levyLaplaceJump_add_measure _ _ hz

theorem tendsto_levyLaplaceSmallControl_zero {z : ℂ} (hz : 0 ≤ z.re) :
    Tendsto (fun n => levyLaplaceJump (levySmallControl η n) z) atTop (𝓝 0) := by
  have hlim (h : ℝ≥0) : Tendsto
      (fun n => (Iio (levyJumpCutoff n)).indicator (levyLaplaceKernel z) h)
      atTop (𝓝 (0 : ℂ)) := by
    by_cases hh : h = 0
    · simp only [hh, Set.indicator_apply, levyLaplaceKernel_zero, ite_self]
      exact tendsto_const_nhds
    · have he : ∀ᶠ n in atTop, levyJumpCutoff n < h :=
        Filter.Tendsto.eventually_lt_const (pos_iff_ne_zero.mpr hh) tendsto_levyJumpCutoff_zero
      have heq : (fun n => (Iio (levyJumpCutoff n)).indicator (levyLaplaceKernel z) h)
          =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
        filter_upwards [he] with n hn
        exact Set.indicator_of_notMem (s := Iio (levyJumpCutoff n))
          (not_lt.mpr hn.le) (levyLaplaceKernel z)
      exact tendsto_const_nhds.congr' heq.symm
  have hd := tendsto_integral_of_dominated_convergence
    (μ := η) (F := fun n => (Iio (levyJumpCutoff n)).indicator (levyLaplaceKernel z))
    (f := fun _ => (0 : ℂ)) (fun _ => 2 + ‖z‖)
    (fun n => ((measurable_levyLaplaceKernel z).indicator measurableSet_Iio).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun h =>
      (norm_indicator_le_norm_self (s := Iio (levyJumpCutoff n))
        (levyLaplaceKernel z) h).trans (norm_levyLaplaceKernel_le hz h))
    (Eventually.of_forall hlim)
  simpa only [levyLaplaceJump, levySmallControl, integral_indicator measurableSet_Iio,
    integral_zero] using hd

theorem tendsto_levyLaplaceLargeControl {z : ℂ} (hz : 0 ≤ z.re) :
    Tendsto (fun n => levyLaplaceJump (levyLargeControl η n) z) atTop
      (𝓝 (levyLaplaceJump η z)) := by
  have he (n : ℕ) : levyLaplaceJump (levyLargeControl η n) z =
      levyLaplaceJump η z - levyLaplaceJump (levySmallControl η n) z := by
    rw [levyLaplaceJump_split η hz n]
    abel
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub
    (tendsto_levyLaplaceSmallControl_zero η hz)

end GaloisForLFunctions.HTGeometry
