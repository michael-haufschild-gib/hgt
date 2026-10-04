import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite-window causal recovery for Route P

The critical prime-delay operator carries a factor `1 / sqrt p`.
These finite-window estimates retain that gain when recovering a
prime-deleted source. They require no square admission on the full ray.
They are ingredients for the native biased-covariance comparison;
they do not bound the native source energy as the window grows.
-/

open MeasureTheory Set

namespace RHTower.RoutePWindow

/-- A causal delay can only decrease square energy on the original window. -/
theorem shift_square_integral_le (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ t ≤ 0, f t = 0) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (f (t-a))^2) ≤ ∫ t in (0 : ℝ)..T, (f t)^2 := by
  have hzero {b c : ℝ} (hbc : b ≤ c) (hc : c ≤ 0) :
      (∫ t in b..c, (f t)^2) = 0 := by
    calc
      _ = ∫ _t in b..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hbc] at ht
        simp [hz t (ht.2.trans hc)]
      _ = 0 := by simp
  rw [intervalIntegral.integral_comp_sub_right (fun t => (f t)^2) a, zero_sub]
  by_cases hTa : 0 ≤ T-a
  · have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hf.pow 2).intervalIntegrable (-a) 0)
      ((hf.pow 2).intervalIntegrable 0 (T-a))
    simp only [Pi.pow_apply] at hadd
    rw [hzero (b := -a) (c := 0) (by linarith) le_rfl, zero_add] at hadd
    rw [← hadd]
    exact intervalIntegral.integral_mono_interval le_rfl hTa (by linarith)
      (Filter.Eventually.of_forall fun t => sq_nonneg (f t))
      ((hf.pow 2).intervalIntegrable 0 T)
  · rw [hzero (by linarith) (by linarith)]
    exact intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg (f t))

/-- Recovery loses only `(1-q)^2`, with the complete earlier-clock square
retained. The hypotheses describe the local source and scalar delay, not
global integrability or an arithmetic cancellation estimate. -/
theorem delay_recovery_square (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ t ≤ 0, f t = 0) {a T q : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1-q)^2 * (∫ t in (0 : ℝ)..T, (f t)^2) ≤
      ∫ t in (0 : ℝ)..T, (f t-q*f (t-a))^2 := by
  have hs : Continuous (fun t => f (t-a)) := hf.comp (continuous_id.sub continuous_const)
  have hh : Continuous (fun t => f t-q*f (t-a)) := hf.sub (hs.const_mul q)
  have hright : Continuous (fun t => (f t-q*f (t-a))^2+q*(1-q)*(f (t-a))^2) :=
    (hh.pow 2).add ((hs.pow 2).const_mul (q*(1-q)))
  have hpoint (t : ℝ) :
      (1-q)*(f t)^2 ≤ (f t-q*f (t-a))^2+q*(1-q)*(f (t-a))^2 := by
    nlinarith [mul_nonneg hq0 (sq_nonneg (f t-f (t-a)))]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((hf.pow 2).const_mul (1-q)).intervalIntegrable 0 T)
    (hright.intervalIntegrable 0 T) (fun t _ => hpoint t)
  simp only [Pi.pow_apply] at hi
  have hhI : IntervalIntegrable (fun t => (f t-q*f (t-a))^2) volume 0 T :=
    (hh.pow 2).intervalIntegrable 0 T
  have hsI : IntervalIntegrable (fun t => q*(1-q)*(f (t-a))^2) volume 0 T :=
    ((hs.pow 2).const_mul (q*(1-q))).intervalIntegrable 0 T
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hhI hsI,
    intervalIntegral.integral_const_mul] at hi
  have hshift := shift_square_integral_le f hf hz ha hT
  have hpaid := mul_le_mul_of_nonneg_left hshift
    (mul_nonneg hq0 (sub_nonneg.mpr hq1))
  nlinarith

end RHTower.RoutePWindow
