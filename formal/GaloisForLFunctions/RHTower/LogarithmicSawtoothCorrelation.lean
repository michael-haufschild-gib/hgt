import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Reflection of reciprocal logarithmic sawtooths

The clocks at `s` and `T-s` run on the reciprocal hyperbola with product
`exp T`. Their product is invariant under reflection. Consequently a
linear weight can be replaced by its midpoint value exactly.
-/

noncomputable section
open MeasureTheory Set

namespace RHTower

def logarithmicCenteredSawtooth (t : ℝ) : ℝ := Int.fract (Real.exp t) - 1 / 2

def logarithmicReciprocalSawtoothCorrelation (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s

theorem abs_logarithmicCenteredSawtooth_le (t : ℝ) :
    |logarithmicCenteredSawtooth t| ≤ 1 / 2 := by
  rw [logarithmicCenteredSawtooth, abs_le]
  constructor <;> linarith [Int.fract_nonneg (Real.exp t), Int.fract_lt_one (Real.exp t)]

theorem measurable_logarithmicCenteredSawtooth : Measurable logarithmicCenteredSawtooth :=
  (measurable_fract.comp Real.measurable_exp).sub_const (1 / 2)

theorem intervalIntegrable_logarithmicCenteredSawtooth (a b : ℝ) :
    IntervalIntegrable logarithmicCenteredSawtooth volume a b := by
  apply (intervalIntegrable_const (c := (1 / 2 : ℝ)) (a := a) (b := b)).mono_fun'
    measurable_logarithmicCenteredSawtooth.aestronglyMeasurable.restrict
  filter_upwards with t
  simpa only [Real.norm_eq_abs] using abs_logarithmicCenteredSawtooth_le t

theorem intervalIntegrable_logarithmicReciprocalSawtooth (T a b : ℝ) :
    IntervalIntegrable
      (fun s => logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s)
      volume a b := by
  have hm : Measurable
      (fun s => logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s) :=
    (measurable_logarithmicCenteredSawtooth.comp (measurable_const.sub measurable_id)).mul
      measurable_logarithmicCenteredSawtooth
  apply (intervalIntegrable_const (c := (1 / 4 : ℝ)) (a := a) (b := b)).mono_fun'
    hm.aestronglyMeasurable.restrict
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (1 / 2 : ℝ) * (1 / 2) := mul_le_mul
      (abs_logarithmicCenteredSawtooth_le _) (abs_logarithmicCenteredSawtooth_le _)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem logarithmicReciprocalSawtooth_weight_reflection (T : ℝ) :
    (∫ s in (0 : ℝ)..T, (T - s - 1) *
      (logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s)) =
        (T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T := by
  let p := fun s => logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s
  have hi : IntervalIntegrable p volume 0 T :=
    intervalIntegrable_logarithmicReciprocalSawtooth T 0 T
  have hl : IntervalIntegrable (fun s => (T - s - 1) * p s) volume 0 T :=
    hi.continuousOn_mul (by fun_prop)
  have hr : IntervalIntegrable (fun s => (s - 1) * p s) volume 0 T :=
    hi.continuousOn_mul (by fun_prop)
  have href : (∫ s in (0 : ℝ)..T, (T - s - 1) * p s) =
      ∫ s in (0 : ℝ)..T, (s - 1) * p s := by
    calc
      _ = ∫ s in (0 : ℝ)..T, (T - (T - s) - 1) * p (T - s) := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left (fun s => (T - s - 1) * p s) T
            (a := 0) (b := T)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only [p]
        rw [sub_sub_cancel]
        ring
  have hsum : (∫ s in (0 : ℝ)..T, (T - s - 1) * p s) +
      (∫ s in (0 : ℝ)..T, (s - 1) * p s) =
        (T - 2) * logarithmicReciprocalSawtoothCorrelation T := by
    rw [← intervalIntegral.integral_add hl hr, logarithmicReciprocalSawtoothCorrelation,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [p, logarithmicReciprocalSawtoothCorrelation]
    ring
  change (∫ s in (0 : ℝ)..T, (T - s - 1) * p s) = _
  linarith only [href, hsum]

theorem abs_logarithmicReciprocalSawtoothCorrelation_le {T : ℝ} (hT : 0 ≤ T) :
    |logarithmicReciprocalSawtoothCorrelation T| ≤ T / 4 := by
  have hi := intervalIntegrable_logarithmicReciprocalSawtooth T 0 T
  calc
    _ ≤ ∫ s in (0 : ℝ)..T,
        |logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s| :=
      intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ _s in (0 : ℝ)..T, (1 / 4 : ℝ) := by
      apply intervalIntegral.integral_mono_on hT hi.abs intervalIntegrable_const
      intro s _
      rw [abs_mul]
      calc
        _ ≤ (1 / 2 : ℝ) * (1 / 2) := mul_le_mul
          (abs_logarithmicCenteredSawtooth_le _) (abs_logarithmicCenteredSawtooth_le _)
          (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := by simp [div_eq_mul_inv]

end RHTower
