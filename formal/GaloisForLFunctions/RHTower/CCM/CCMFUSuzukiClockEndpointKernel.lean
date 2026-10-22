import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter Topology

namespace RHTower

noncomputable section

private theorem ccmSuzukiCubicClockEndpointKernel_lower_local
    {δ ω : ℝ} (hδ : 0 < δ) (hω : 0 < ω) :
    1 / (16 * ω ^ 3 * δ) ≤
      ∫ v in (0 : ℝ)..(δ / ω),
        3 * v ^ 2 / (δ + ω * v) ^ 4 := by
  let a : ℝ := δ / ω
  have ha : 0 ≤ a := le_of_lt (div_pos hδ hω)
  have hden : ∀ v ∈ Set.Icc (0 : ℝ) a, 0 < δ + ω * v := by
    intro v hv
    exact add_pos_of_pos_of_nonneg hδ (mul_nonneg hω.le hv.1)
  have hfi : IntervalIntegrable
      (fun v : ℝ => 3 * v ^ 2 / (δ + ω * v) ^ 4)
      volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    exact (continuousAt_const.mul (continuousAt_id.pow 2)).continuousWithinAt.div
      ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).pow 4).continuousWithinAt
      (pow_ne_zero 4 (hden v (by simpa only [Set.uIcc_of_le ha] using hv)).ne')
  have hgi : IntervalIntegrable
      (fun v : ℝ => 3 * v ^ 2 / (16 * δ ^ 4))
      volume 0 a := by
    have hc : Continuous (fun v : ℝ => 3 * v ^ 2 / (16 * δ ^ 4)) := by
      fun_prop
    exact hc.intervalIntegrable 0 a
  have hpoint : ∀ v ∈ Set.Icc (0 : ℝ) a,
      3 * v ^ 2 / (16 * δ ^ 4) ≤
        3 * v ^ 2 / (δ + ω * v) ^ 4 := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have htop : δ + ω * v ≤ 2 * δ := by
      have hvle : v ≤ δ / ω := hv.2
      have hwv : ω * v ≤ δ := by
        have h := mul_le_mul_of_nonneg_left hvle hω.le
        simpa [mul_div_cancel₀ δ hω.ne'] using h
      linarith
    have hpow : (δ + ω * v) ^ 4 ≤ 16 * δ ^ 4 := by
      nlinarith [pow_le_pow_left₀ (hden v hv).le htop 4]
    have hden1 : 0 < 16 * δ ^ 4 := by positivity
    have hden2 : 0 < (δ + ω * v) ^ 4 := by positivity
    apply (div_le_div_iff₀ hden1 hden2).2
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hmono := intervalIntegral.integral_mono_on ha hgi hfi hpoint
  have hpoly :
      (∫ v in (0 : ℝ)..a, 3 * v ^ 2 / (16 * δ ^ 4)) =
        1 / (16 * ω ^ 3 * δ) := by
    calc
      _ = (3 / (16 * δ ^ 4)) * (∫ v in (0 : ℝ)..a, v ^ 2) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext v
        ring
      _ = _ := by
        rw [integral_pow]
        dsimp [a]
        field_simp [hδ.ne', hω.ne']
        ring
  rw [hpoly] at hmono
  exact hmono

/-- The cubic positive Suzuki clock retains at least inverse-distance endpoint mass
in the third derivative of its Cauchy transform. -/
theorem ccmSuzukiCubicClockEndpointKernel_lower
    {δ ω : ℝ} (hδ : 0 < δ) (hω : 0 < ω) (hδω : δ ≤ ω) :
    1 / (16 * ω ^ 3 * δ) ≤
      ∫ v in (0 : ℝ)..1,
        3 * v ^ 2 / (δ + ω * v) ^ 4 := by
  have ha0 : 0 ≤ δ / ω := le_of_lt (div_pos hδ hω)
  have ha1 : δ / ω ≤ 1 := (div_le_one hω).2 hδω
  have hfi : IntervalIntegrable
      (fun v : ℝ => 3 * v ^ 2 / (δ + ω * v) ^ 4)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le h01] using hv
    have hv0 : 0 ≤ v := hv'.1
    have hden : δ + ω * v ≠ 0 :=
      (add_pos_of_pos_of_nonneg hδ (mul_nonneg hω.le hv0)).ne'
    exact (continuousAt_const.mul (continuousAt_id.pow 2)).continuousWithinAt.div
      ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).pow 4).continuousWithinAt
      (pow_ne_zero 4 hden)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun v : ℝ => 3 * v ^ 2 / (δ + ω * v) ^ 4) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hv0 : 0 ≤ v := hv.1.le
    positivity
  have hmono := intervalIntegral.integral_mono_interval
    (c := (0 : ℝ)) (d := (1 : ℝ)) le_rfl ha0 ha1 hnonneg hfi
  exact (ccmSuzukiCubicClockEndpointKernel_lower_local hδ hω).trans hmono

/-- The endpoint kernel diverges as the spectral point approaches the transported
rightmost divisor endpoint from the right. This is an analytic kernel theorem, not yet
a statement about the literal prime--polar source. -/
theorem ccmSuzukiCubicClockEndpointKernel_tendsto_atTop {ω : ℝ} (hω : 0 < ω) :
    Tendsto
      (fun δ : ℝ => ∫ v in (0 : ℝ)..1,
        3 * v ^ 2 / (δ + ω * v) ^ 4)
      (𝓝[>] 0) atTop := by
  have hcoeff : 0 < 1 / (16 * ω ^ 3) := by positivity
  have hlow : Tendsto (fun δ : ℝ => δ⁻¹ * (1 / (16 * ω ^ 3)))
      (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_mul_pos hcoeff tendsto_const_nhds
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _ hlow
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hω] with δ hδ hδω
  have hbound := ccmSuzukiCubicClockEndpointKernel_lower hδ (hω := hω) hδω.2.le
  have hiden : δ⁻¹ * (1 / (16 * ω ^ 3)) =
      1 / (16 * ω ^ 3 * δ) := by
    have hδ' : 0 < δ := hδ
    field_simp [hδ'.ne', hω.ne']
  rw [hiden]
  exact hbound

end

end RHTower

