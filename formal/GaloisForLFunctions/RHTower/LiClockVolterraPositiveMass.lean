import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Positive mass from a monotone Volterra kernel

A positive nondecreasing kernel bounds the Volterra response by the accumulated
positive part of its input. An unbounded response-to-kernel ratio forces
unbounded positive mass and cofinal positive values. The exact quadratic clock
substitution retains the response factor and transfers this divergence to the
clock density. All compact-interval integrability follows from continuity.
-/

open MeasureTheory Set Filter Topology

namespace RHTower
noncomputable section

/-- The accumulated positive part of a continuous function is nondecreasing on the real line. -/
theorem liClock_positivePartIntegral_monotone
    {F : ℝ → ℝ} (hF : Continuous F) :
    Monotone (fun t : ℝ => ∫ s in (0 : ℝ)..t, max (F s) 0) := by
  have hp : Continuous (fun s => max (F s) 0) := hF.max continuous_const
  intro a b hab
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hp.intervalIntegrable 0 a) (hp.intervalIntegrable a b)
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun s => le_max_right (F s) 0)
  linarith

/-- A positive nondecreasing Volterra kernel gives a lower bound for positive-part mass. -/
theorem liClockVolterra_positivePartIntegral_ge_ratio
    {F B D : ℝ → ℝ} (hF : Continuous F) (hB : Continuous B)
    (hBpos : ∀ t ∈ Ici (0 : ℝ), 0 < B t)
    (hBmono : MonotoneOn B (Ici (0 : ℝ)))
    (hconv : ∀ t ∈ Ici (0 : ℝ),
      (∫ s in (0 : ℝ)..t, F s * B (t - s)) = D t)
    {t : ℝ} (ht : 0 < t) :
    D t / B t ≤ ∫ s in (0 : ℝ)..t, max (F s) 0 := by
  have hfc : Continuous (fun s => F s * B (t - s)) :=
    hF.mul (hB.comp (continuous_const.sub continuous_id))
  have hpc : Continuous (fun s => max (F s) 0 * B t) :=
    (hF.max continuous_const).mul continuous_const
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht.le
    (hfc.intervalIntegrable 0 t) (hpc.intervalIntegrable 0 t)
    (fun s hs => calc
      F s * B (t - s) ≤ max (F s) 0 * B (t - s) :=
        mul_le_mul_of_nonneg_right (le_max_left (F s) 0)
          (hBpos (t - s) (by change 0 ≤ t - s; linarith [hs.2])).le
      _ ≤ max (F s) 0 * B t :=
        mul_le_mul_of_nonneg_left
          (hBmono (by change 0 ≤ t - s; linarith [hs.2]) ht.le
            (by linarith [hs.1])) (le_max_right (F s) 0))
  rw [hconv t ht.le, intervalIntegral.integral_mul_const] at hi
  exact (div_le_iff₀ (hBpos t ht.le)).2 hi

/-- A divergent response-to-kernel ratio forces divergent positive-part mass. -/
theorem liClockVolterra_tendsto_positivePartIntegral_atTop
    {F B D : ℝ → ℝ} (hF : Continuous F) (hB : Continuous B)
    (hBpos : ∀ t ∈ Ici (0 : ℝ), 0 < B t)
    (hBmono : MonotoneOn B (Ici (0 : ℝ)))
    (hconv : ∀ t ∈ Ici (0 : ℝ),
      (∫ s in (0 : ℝ)..t, F s * B (t - s)) = D t)
    (hratio : Tendsto (fun t => D t / B t) atTop atTop) :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, max (F s) 0) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hratio
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact liClockVolterra_positivePartIntegral_ge_ratio hF hB hBpos hBmono hconv ht

/-- Divergent positive-part mass forces positive values beyond every real threshold. -/
theorem liClock_positive_cofinally_of_tendsto_positivePartIntegral
    {F : ℝ → ℝ} (hF : Continuous F)
    (hmass : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, max (F s) 0) atTop atTop) :
    ∀ T : ℝ, ∃ t > T, 0 < F t := by
  have hp : Continuous (fun s => max (F s) 0) := hF.max continuous_const
  intro T
  by_contra h
  have hnon : ∀ s : ℝ, T < s → F s ≤ 0 := by
    intro s hs
    by_contra hpos
    exact h ⟨s, hs, lt_of_not_ge hpos⟩
  obtain ⟨t, htlarge, ht⟩ :=
    ((hmass.eventually_ge_atTop ((∫ s in (0 : ℝ)..T, max (F s) 0) + 1)).and
      (eventually_gt_atTop T)).exists
  have hz : (∫ s in T..t, max (F s) 0) = 0 := by
    calc
      (∫ s in T..t, max (F s) 0) = ∫ _s in T..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.le
        intro s hs
        exact max_eq_right (hnon s hs.1)
      _ = 0 := by simp
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hp.intervalIntegrable 0 T) (hp.intervalIntegrable T t)
  rw [hz] at hi
  linarith

/-- A divergent response-to-kernel ratio forces cofinal positive input values. -/
theorem liClockVolterra_positive_cofinally
    {F B D : ℝ → ℝ} (hF : Continuous F) (hB : Continuous B)
    (hBpos : ∀ t ∈ Ici (0 : ℝ), 0 < B t)
    (hBmono : MonotoneOn B (Ici (0 : ℝ)))
    (hconv : ∀ t ∈ Ici (0 : ℝ),
      (∫ s in (0 : ℝ)..t, F s * B (t - s)) = D t)
    (hratio : Tendsto (fun t => D t / B t) atTop atTop) :
    ∀ T : ℝ, ∃ t > T, 0 < F t := by
  exact liClock_positive_cofinally_of_tendsto_positivePartIntegral hF
    (liClockVolterra_tendsto_positivePartIntegral_atTop hF hB hBpos hBmono hconv hratio)

/-- Exact positive-part substitution for the response s * S(s^2 / 16), including s = 0. -/
theorem liClock_positivePartIntegral_eq_eight_mul
    {S : ℝ → ℝ} (hS : Continuous S) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, max (s * S (s ^ 2 / 16)) 0) =
      8 * ∫ w in (0 : ℝ)..(t ^ 2 / 16), max (S w) 0 := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun x : ℝ => x ^ 2 / 16) (s / 8) s := by
    intro s _
    have h := ((hasDerivAt_id s).mul (hasDerivAt_id s)).div_const (16 : ℝ)
    simpa only [pow_two, Pi.mul_apply, id_eq] using
      h.congr_deriv (by simp only [id_eq]; ring)
  have hf' : ContinuousOn (fun s : ℝ => s / 8) (uIcc (0 : ℝ) t) :=
    (continuous_id.div_const (8 : ℝ)).continuousOn
  have hc := intervalIntegral.integral_comp_mul_deriv
    (g := fun w => max (S w) 0) hd hf' (hS.max continuous_const)
  simp only [Function.comp_apply, zero_pow (by norm_num : 2 ≠ 0), zero_div] at hc
  calc
    (∫ s in (0 : ℝ)..t, max (s * S (s ^ 2 / 16)) 0) =
        ∫ s in (0 : ℝ)..t, 8 * (max (S (s ^ 2 / 16)) 0 * (s / 8)) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht]
      intro s hs
      change max (s * S (s ^ 2 / 16)) 0 =
        8 * (max (S (s ^ 2 / 16)) 0 * (s / 8))
      have he : max (s * S (s ^ 2 / 16)) 0 = s * max (S (s ^ 2 / 16)) 0 := by
        simpa only [mul_comm, zero_mul, mul_zero] using
          (max_mul_of_nonneg (S (s ^ 2 / 16)) 0 hs.1).symm
      rw [he]
      ring
    _ = 8 * ∫ s in (0 : ℝ)..t, max (S (s ^ 2 / 16)) 0 * (s / 8) :=
      intervalIntegral.integral_const_mul _ _
    _ = 8 * ∫ w in (0 : ℝ)..(t ^ 2 / 16), max (S w) 0 := by rw [hc]

/-- Divergent response mass transfers to the clock density through attained clocks and monotonicity. -/
theorem liClock_tendsto_positivePartIntegral_atTop
    {S : ℝ → ℝ} (hS : Continuous S)
    (hmass : Tendsto (fun t : ℝ =>
      ∫ s in (0 : ℝ)..t, max (s * S (s ^ 2 / 16)) 0) atTop atTop) :
    Tendsto (fun w : ℝ => ∫ z in (0 : ℝ)..w, max (S z) 0) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨t, hlarge, ht⟩ :=
    ((hmass.eventually_ge_atTop (8 * b)).and (eventually_ge_atTop (0 : ℝ))).exists
  rw [liClock_positivePartIntegral_eq_eight_mul hS ht] at hlarge
  have hbound : b ≤ ∫ w in (0 : ℝ)..(t ^ 2 / 16), max (S w) 0 := by linarith
  filter_upwards [eventually_ge_atTop (t ^ 2 / 16)] with w hw
  exact hbound.trans (liClock_positivePartIntegral_monotone hS hw)

end
end RHTower
