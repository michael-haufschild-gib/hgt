import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous Cesàro integral asymptotics

A continuous function tending to zero has a sublinear primitive. This dependency-neutral form is
shared by logarithmic density asymptotics and vertical-phase asymptotics.
-/

open Filter Topology intervalIntegral MeasureTheory

namespace HTGeometry

/-- A continuous function tending to zero at infinity has a sublinear primitive. -/
theorem tendsto_integral_div_atTop {ε : ℝ → ℝ} (hcont : ContinuousOn ε (Set.Ici 1))
    (h : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun T => (∫ t in (1 : ℝ)..T, ε t) / T) atTop (𝓝 0) := by
  have hint : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable ε volume a b := by
    intro a b ha hb
    refine (hcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc, Set.mem_Icc] at hx
    exact le_trans (le_min ha hb) hx.1
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp h) (δ / 2) hhalf
  set T₁ : ℝ := max T₀ 1 with hT₁
  have hT₁1 : (1 : ℝ) ≤ T₁ := le_max_right _ _
  set A : ℝ := |∫ t in (1 : ℝ)..T₁, ε t| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  refine ⟨max T₁ (2 * A / δ + 1), fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTA : 2 * A / δ + 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by
    have : (1 : ℝ) ≤ T := le_trans hT₁1 hTT₁
    linarith
  have hsplit : (∫ t in (1 : ℝ)..T, ε t)
      = (∫ t in (1 : ℝ)..T₁, ε t) + ∫ t in T₁..T, ε t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 1 T₁ (le_refl _) hT₁1)
      (hint T₁ T hT₁1 (le_trans hT₁1 hTT₁))]
  have htail : |∫ t in T₁..T, ε t| ≤ δ / 2 * (T - T₁) := by
    have hbound : ∀ t ∈ Set.uIoc T₁ T, ‖ε t‖ ≤ δ / 2 := by
      intro t ht
      rw [Set.uIoc_of_le hTT₁] at ht
      have hge : T₀ ≤ t := le_trans (le_max_left _ _) (le_of_lt ht.1)
      have := hT₀ t hge
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := δ / 2) hbound
    rw [Real.norm_eq_abs] at this
    calc |∫ t in T₁..T, ε t| ≤ δ / 2 * |T - T₁| := this
      _ = δ / 2 * (T - T₁) := by rw [abs_of_nonneg (by linarith)]
  have hnum : |∫ t in (1 : ℝ)..T, ε t| ≤ A + δ / 2 * T := by
    rw [hsplit]
    calc |(∫ t in (1 : ℝ)..T₁, ε t) + ∫ t in T₁..T, ε t|
        ≤ A + |∫ t in T₁..T, ε t| := abs_add_le _ _
      _ ≤ A + δ / 2 * (T - T₁) := by linarith [htail]
      _ ≤ A + δ / 2 * T := by nlinarith [hT₁1, hδ]
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hT0, div_lt_iff₀ hT0]
  have hAT : A < δ / 2 * T := by
    have h1 : 2 * A / δ < T := by linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  linarith [hnum]

/-- Moving the fixed lower endpoint from `1` to `A` and normalizing by interval length preserves
the vanishing Cesàro limit. -/
theorem tendsto_intervalIntegral_div_sub_atTop {e : ℝ → ℝ} (hcont : Continuous e)
    (he : Tendsto e atTop (𝓝 0)) (A : ℝ) :
    Tendsto (fun T => (∫ u in A..T, e u) / (T - A)) atTop (𝓝 0) := by
  have hbase := tendsto_integral_div_atTop hcont.continuousOn he
  have hden : Tendsto (fun T : ℝ => T - A) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-A) (tendsto_id : Tendsto id atTop atTop)
  have hconst : Tendsto (fun T : ℝ => (∫ u in A..(1 : ℝ), e u) / (T - A))
      atTop (𝓝 0) := hden.const_div_atTop _
  have hsmall : Tendsto (fun T : ℝ => A / (T - A)) atTop (𝓝 0) :=
    hden.const_div_atTop A
  have hratio : Tendsto (fun T : ℝ => T / (T - A)) atTop (𝓝 1) := by
    have hadd := hsmall.add_const 1
    have hadd' : Tendsto (fun T : ℝ => A / (T - A) + 1) atTop (𝓝 1) := by
      simpa only [zero_add] using hadd
    refine Filter.Tendsto.congr' ?_ hadd'
    filter_upwards [eventually_gt_atTop A] with T hT
    field_simp
    ring
  have hlim : Tendsto (fun T : ℝ =>
      (∫ u in A..(1 : ℝ), e u) / (T - A) +
        ((∫ u in (1 : ℝ)..T, e u) / T) * (T / (T - A))) atTop (𝓝 0) := by
    simpa only [zero_mul, add_zero] using hconst.add (hbase.mul hratio)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (max 1 (A + 1))] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTA : A < T := lt_of_lt_of_le (lt_add_one A) (le_trans (le_max_right _ _) hT)
  have hsplit : (∫ u in A..T, e u) =
      (∫ u in A..(1 : ℝ), e u) + ∫ u in (1 : ℝ)..T, e u := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable A 1) (hcont.intervalIntegrable 1 T)]
  rw [hsplit]
  field_simp

/-- Integral Cesàro theorem with an arbitrary finite limit and fixed lower endpoint. -/
theorem tendsto_intervalAverage_atTop_of_tendsto {f : ℝ → ℝ} (hcont : Continuous f)
    {c : ℝ} (hf : Tendsto f atTop (𝓝 c)) (A : ℝ) :
    Tendsto (fun T => (∫ u in A..T, f u) / (T - A)) atTop (𝓝 c) := by
  let e : ℝ → ℝ := fun u => f u - c
  have hecont : Continuous e := hcont.sub continuous_const
  have he : Tendsto e atTop (𝓝 0) := by simpa [e] using hf.sub_const c
  have havg := tendsto_intervalIntegral_div_sub_atTop hecont he A
  have hlim : Tendsto (fun T : ℝ => c + (∫ u in A..T, e u) / (T - A))
      atTop (𝓝 c) := by
    simpa only [add_zero] using (tendsto_const_nhds.add havg)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop A] with T hT
  have hne : T - A ≠ 0 := sub_ne_zero.mpr hT.ne'
  rw [show (∫ u in A..T, f u) = c * (T - A) + ∫ u in A..T, e u by
    change (∫ u in A..T, f u) = c * (T - A) + ∫ u in A..T, f u - c
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable A T)
      (continuous_const.intervalIntegrable A T), intervalIntegral.integral_const]
    ring]
  field_simp

end HTGeometry
