import GaloisForLFunctions.RHTower.LogarithmicSawtoothCorrelation

/-!
# Correlation of two causal sawtooth entries

Two entries restrict the integration window to the interval between
their arrival times. Translation identifies its integral with the
literal reciprocal correlation at the remaining time.
-/

noncomputable section
open MeasureTheory Set

namespace RHTower

def logarithmicSawtoothEntry (p t : ℝ) : ℝ :=
  (Ici p).indicator (fun s => logarithmicCenteredSawtooth (s - p)) t

theorem measurable_logarithmicSawtoothEntry (p : ℝ) :
    Measurable (logarithmicSawtoothEntry p) :=
  (measurable_logarithmicCenteredSawtooth.comp (measurable_id.sub_const p)).indicator
    measurableSet_Ici

theorem abs_logarithmicSawtoothEntry_le (p t : ℝ) :
    |logarithmicSawtoothEntry p t| ≤ 1 / 2 := by
  by_cases h : p ≤ t
  · simpa [logarithmicSawtoothEntry, h] using
      abs_logarithmicCenteredSawtooth_le (t - p)
  · simp [logarithmicSawtoothEntry, h]

theorem intervalIntegrable_logarithmicSawtoothEntry_pair (p q T a b : ℝ) :
    IntervalIntegrable
      (fun s => logarithmicSawtoothEntry p s * logarithmicSawtoothEntry q (T - s))
      volume a b := by
  have hm : Measurable
      (fun s => logarithmicSawtoothEntry p s * logarithmicSawtoothEntry q (T - s)) :=
    (measurable_logarithmicSawtoothEntry p).mul
      ((measurable_logarithmicSawtoothEntry q).comp (measurable_const.sub measurable_id))
  apply (intervalIntegrable_const (c := (1 / 4 : ℝ)) (a := a) (b := b)).mono_fun'
    hm.aestronglyMeasurable.restrict
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (1 / 2 : ℝ) * (1 / 2) := mul_le_mul
      (abs_logarithmicSawtoothEntry_le _ _) (abs_logarithmicSawtoothEntry_le _ _)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem integral_closed_window (f : ℝ → ℝ) {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ s in (0 : ℝ)..T, (Icc a b).indicator f s) = ∫ s in a..b, f s := by
  rw [intervalIntegral.integral_of_le ((ha.trans hab).trans hb),
    ← integral_Icc_eq_integral_Ioc,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc ha hb), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

theorem integral_logarithmicSawtoothEntry_pair {p q T : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ T) :
    (∫ s in (0 : ℝ)..T,
      logarithmicSawtoothEntry p s * logarithmicSawtoothEntry q (T - s)) =
        logarithmicReciprocalSawtoothCorrelation (T - p - q) := by
  have hpoint (s : ℝ) :
      logarithmicSawtoothEntry p s * logarithmicSawtoothEntry q (T - s) =
        (Icc p (T - q)).indicator
          (fun u => logarithmicCenteredSawtooth (u - p) *
            logarithmicCenteredSawtooth (T - u - q)) s := by
    have hcut : q ≤ T - s ↔ s ≤ T - q := by constructor <;> intro h <;> linarith
    by_cases hs : p ≤ s <;> by_cases ht : s ≤ T - q <;>
      simp [logarithmicSawtoothEntry, Set.indicator, hcut, hs, ht]
  simp_rw [hpoint]
  rw [integral_closed_window _ hp (by linarith only [hpq]) (by linarith only [hq])]
  calc
    _ = ∫ s in p..(T - q),
        (fun u => logarithmicCenteredSawtooth u *
          logarithmicCenteredSawtooth (T - p - q - u)) (s - p) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [show T - p - q - (s - p) = T - s - q by ring]
    _ = ∫ s in (0 : ℝ)..(T - p - q),
        logarithmicCenteredSawtooth s * logarithmicCenteredSawtooth (T - p - q - s) := by
      rw [intervalIntegral.integral_comp_sub_right
        (fun u => logarithmicCenteredSawtooth u * logarithmicCenteredSawtooth (T - p - q - u)),
        sub_self, show T - q - p = T - p - q by ring]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      exact mul_comm _ _

end RHTower
