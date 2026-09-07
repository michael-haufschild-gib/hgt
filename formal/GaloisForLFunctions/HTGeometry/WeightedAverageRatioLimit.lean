import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weighted averages of a function asymptotic to the identity

If `S(t)/t → 1` and `w ≥ 0` is continuous on `[1, ∞)`, then

* `∫_1^x S w / ∫_1^x t w → 1` provided `∫_1^x t w → ∞` (the initial segment is absorbed);
* `∫_x^∞ S w / ∫_x^∞ t w → 1` provided both integrals exist and the denominator is positive.

These are the two forms of the Abel-summation limit used to evaluate prime power moments from
the prime number theorem: after summation by parts, a weighted prime sum is a boundary term plus
an integral of `ψ` (or `θ`) against a weight, and `ψ(t) ~ t` turns that integral into the
corresponding integral of `t`.
-/

open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- **Weighted averages on `[1, x]`.** -/
theorem tendsto_integral_mul_div_of_tendsto_div
    {S : ℝ → ℝ} (hS : Monotone S)
    (hlim : Tendsto (fun t : ℝ => S t / t) atTop (𝓝 1))
    {w : ℝ → ℝ} (hw : ContinuousOn w (Ici 1)) (hw0 : ∀ t, 1 ≤ t → 0 ≤ w t)
    (hW : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, t * w t) atTop atTop) :
    Tendsto (fun x : ℝ => (∫ t in (1 : ℝ)..x, S t * w t) / ∫ t in (1 : ℝ)..x, t * w t)
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the threshold beyond which `|S t − t| ≤ (ε/3) t`
  obtain ⟨u₀, hu₀⟩ := (Metric.tendsto_atTop.mp hlim) (ε / 3) (by positivity)
  set u₁ := max u₀ 1 with hu₁
  have hu₁1 : (1 : ℝ) ≤ u₁ := le_max_right _ _
  have hSbound : ∀ t, u₁ ≤ t → |S t - t| ≤ ε / 3 * t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos (hu₁1.trans ht)
    have h := hu₀ t ((le_max_left _ _).trans ht)
    rw [Real.dist_eq, show S t / t - 1 = (S t - t) / t by field_simp, abs_div,
      abs_of_pos ht0, div_lt_iff₀ ht0] at h
    exact h.le
  -- integrability facts
  have hwOn : ∀ a b : ℝ, 1 ≤ a → a ≤ b → ContinuousOn w (uIcc a b) := by
    intro a b ha hab
    refine hw.mono ?_
    rw [uIcc_of_le hab]
    intro t ht
    exact ha.trans ht.1
  have hSint : ∀ a b, IntervalIntegrable S volume a b := fun a b => hS.intervalIntegrable
  have hSw : ∀ a b, 1 ≤ a → a ≤ b → IntervalIntegrable (fun t => S t * w t) volume a b :=
    fun a b ha hab => (hSint a b).mul_continuousOn (hwOn a b ha hab)
  have htw : ∀ a b, 1 ≤ a → a ≤ b → IntervalIntegrable (fun t => t * w t) volume a b :=
    fun a b ha hab => (continuous_id.intervalIntegrable a b).mul_continuousOn (hwOn a b ha hab)
  have hdInt : ∀ a b, 1 ≤ a → a ≤ b →
      IntervalIntegrable (fun t => (S t - t) * w t) volume a b := fun a b ha hab =>
    ((hSw a b ha hab).sub (htw a b ha hab)).congr fun t _ => by
      show S t * w t - t * w t = (S t - t) * w t
      ring
  -- the fixed initial-segment error
  set K : ℝ := ∫ t in (1 : ℝ)..u₁, |S t - t| * w t with hK
  have hK0 : 0 ≤ K := intervalIntegral.integral_nonneg hu₁1 fun t ht =>
    mul_nonneg (abs_nonneg _) (hw0 t ht.1)
  -- the denominator is eventually large
  obtain ⟨x₁, hx₁⟩ := (Metric.tendsto_atTop.mp hlim) 1 one_pos
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hW.eventually_ge_atTop (3 * K / ε + 1))
  refine ⟨max x₀ u₁, fun x hx => ?_⟩
  have hxu : u₁ ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := hu₁1.trans hxu
  have hWx : 3 * K / ε + 1 ≤ ∫ t in (1 : ℝ)..x, t * w t := hx₀ x ((le_max_left _ _).trans hx)
  have hWpos : 0 < ∫ t in (1 : ℝ)..x, t * w t := by
    have : 0 ≤ 3 * K / ε := by positivity
    linarith
  set W := ∫ t in (1 : ℝ)..x, t * w t with hWdef
  -- the numerator minus the denominator
  have hdiff : (∫ t in (1 : ℝ)..x, S t * w t) - W
      = ∫ t in (1 : ℝ)..x, (S t - t) * w t := by
    rw [hWdef, ← intervalIntegral.integral_sub (hSw 1 x le_rfl hx1) (htw 1 x le_rfl hx1)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  -- split at `u₁`
  have hsplit : ∫ t in (1 : ℝ)..x, (S t - t) * w t
      = (∫ t in (1 : ℝ)..u₁, (S t - t) * w t) + ∫ t in u₁..x, (S t - t) * w t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hdInt 1 u₁ le_rfl hu₁1)
      (hdInt u₁ x hu₁1 hxu)]
  have h1 : |∫ t in (1 : ℝ)..u₁, (S t - t) * w t| ≤ K := by
    refine (intervalIntegral.abs_integral_le_integral_abs hu₁1).trans ?_
    rw [hK]
    refine intervalIntegral.integral_mono_on hu₁1 (hdInt 1 u₁ le_rfl hu₁1).abs ?_ fun t ht => ?_
    · exact ((hSint 1 u₁).sub (continuous_id.intervalIntegrable _ _)).abs.mul_continuousOn
        (hwOn 1 u₁ le_rfl hu₁1)
    · rw [abs_mul, abs_of_nonneg (hw0 t ht.1)]
  have h2 : |∫ t in u₁..x, (S t - t) * w t| ≤ ε / 3 * W := by
    refine (intervalIntegral.abs_integral_le_integral_abs hxu).trans ?_
    have hle : ∫ t in u₁..x, |(S t - t) * w t| ≤ ∫ t in u₁..x, ε / 3 * (t * w t) := by
      refine intervalIntegral.integral_mono_on hxu (hdInt u₁ x hu₁1 hxu).abs
        ((htw u₁ x hu₁1 hxu).const_mul _) fun t ht => ?_
      rw [abs_mul, abs_of_nonneg (hw0 t (hu₁1.trans ht.1))]
      have := hSbound t ht.1
      have hw' := hw0 t (hu₁1.trans ht.1)
      nlinarith
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hmono : ∫ t in u₁..x, t * w t ≤ W := by
      rw [hWdef, ← intervalIntegral.integral_add_adjacent_intervals (htw 1 u₁ le_rfl hu₁1)
        (htw u₁ x hu₁1 hxu)]
      have : 0 ≤ ∫ t in (1 : ℝ)..u₁, t * w t :=
        intervalIntegral.integral_nonneg hu₁1 fun t ht => mul_nonneg (by linarith [ht.1]) (hw0 t ht.1)
      linarith
    have : 0 ≤ ε / 3 := by positivity
    nlinarith
  -- assemble
  rw [Real.dist_eq, show (∫ t in (1 : ℝ)..x, S t * w t) / W - 1
      = ((∫ t in (1 : ℝ)..x, S t * w t) - W) / W by field_simp, hdiff, hsplit, abs_div,
    abs_of_pos hWpos, div_lt_iff₀ hWpos]
  have hKW : K ≤ ε / 3 * W := by
    have : 3 * K / ε ≤ W - 1 := by linarith
    have := (div_le_iff₀ hε).mp this
    nlinarith
  calc |(∫ t in (1 : ℝ)..u₁, (S t - t) * w t) + ∫ t in u₁..x, (S t - t) * w t|
      ≤ |∫ t in (1 : ℝ)..u₁, (S t - t) * w t| + |∫ t in u₁..x, (S t - t) * w t| := abs_add_le _ _
    _ ≤ K + ε / 3 * W := add_le_add h1 h2
    _ < ε * W := by nlinarith

/-- **Weighted averages on `[x, ∞)`.**  The weight need only be non-negative beyond `t₀`. -/
theorem tendsto_integral_Ioi_mul_div_of_tendsto_div
    {S : ℝ → ℝ}
    (hlim : Tendsto (fun t : ℝ => S t / t) atTop (𝓝 1))
    {w : ℝ → ℝ} {t₀ : ℝ} (ht₀ : 1 ≤ t₀) (hw0 : ∀ t, t₀ ≤ t → 0 ≤ w t)
    (hint : ∀ x, t₀ ≤ x → IntegrableOn (fun t => t * w t) (Ioi x))
    (hSint : ∀ x, t₀ ≤ x → IntegrableOn (fun t => S t * w t) (Ioi x))
    (hWpos : ∀ x, t₀ ≤ x → 0 < ∫ t in Ioi x, t * w t) :
    Tendsto (fun x : ℝ => (∫ t in Ioi x, S t * w t) / ∫ t in Ioi x, t * w t)
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨u₀, hu₀⟩ := (Metric.tendsto_atTop.mp hlim) (ε / 2) (by positivity)
  refine ⟨max u₀ t₀, fun x hx => ?_⟩
  have hxt : t₀ ≤ x := (le_max_right _ _).trans hx
  have hx1 : (1 : ℝ) ≤ x := ht₀.trans hxt
  have hSbound : ∀ t, x ≤ t → |S t - t| ≤ ε / 2 * t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos (hx1.trans ht)
    have h := hu₀ t (((le_max_left _ _).trans hx).trans ht)
    rw [Real.dist_eq, show S t / t - 1 = (S t - t) / t by field_simp, abs_div,
      abs_of_pos ht0, div_lt_iff₀ ht0] at h
    exact h.le
  have hWpos' := hWpos x hxt
  set W := ∫ t in Ioi x, t * w t with hWdef
  have hdiff : (∫ t in Ioi x, S t * w t) - W = ∫ t in Ioi x, (S t - t) * w t := by
    rw [hWdef, ← integral_sub (hSint x hxt) (hint x hxt)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  have hbound : |∫ t in Ioi x, (S t - t) * w t| ≤ ε / 2 * W := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hdint : IntegrableOn (fun t => (S t - t) * w t) (Ioi x) := by
      refine ((hSint x hxt).sub (hint x hxt)).congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp [sub_mul]
    calc ∫ t in Ioi x, ‖(S t - t) * w t‖
        ≤ ∫ t in Ioi x, ε / 2 * (t * w t) := by
          refine setIntegral_mono_on hdint.norm ((hint x hxt).const_mul _) measurableSet_Ioi
            fun t ht => ?_
          have ht' : x ≤ t := (mem_Ioi.mp ht).le
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 t (hxt.trans ht'))]
          have := hSbound t ht'
          have hw' := hw0 t (hxt.trans ht')
          nlinarith
      _ = ε / 2 * W := by rw [integral_const_mul]
  rw [Real.dist_eq, show (∫ t in Ioi x, S t * w t) / W - 1
      = ((∫ t in Ioi x, S t * w t) - W) / W by field_simp, hdiff, abs_div, abs_of_pos hWpos',
    div_lt_iff₀ hWpos']
  nlinarith

end GaloisForLFunctions.HTGeometry
