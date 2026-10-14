import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBesselBoundary

/-!
# `K₀` at the logarithmic edge: divergence and a common singularity

From the logarithmic trace `K₀(cy)/log y → −1` as `y → 0⁺`
(`WeilHigherDenominator.tendsto_kMoment_zero_mul_div_log`):

* `tendsto_kMoment_zero_nhdsGT`: `K₀(r) → ∞` as `r → 0⁺`;
* `tendsto_kMoment_zero_mul_div`: `K₀(ar)/K₀(r) → 1` as `r → 0⁺`, for every `a > 0`.

So all `K₀(c y)`, `c > 0`, carry the same logarithmic singularity at `y = 0`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.BesselKZero

theorem eventually_log_ne_zero_nhdsGT : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log r ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 from
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with r hr hr1
  exact (Real.log_neg hr hr1).ne

/-- `K₀(r) → ∞` as `r → 0⁺`. -/
theorem tendsto_kMoment_zero_nhdsGT : Tendsto (kMoment 0) (𝓝[>] 0) atTop := by
  have h := WeilHigherDenominator.tendsto_kMoment_zero_mul_div_log (c := 1) one_pos
  have hprod := Tendsto.neg_mul_atBot (by norm_num : (-1 : ℝ) < 0) h Real.tendsto_log_nhdsGT_zero
  refine hprod.congr' ?_
  filter_upwards [eventually_log_ne_zero_nhdsGT] with r hr
  simp only [one_mul]
  field_simp

/-- **Common logarithmic singularity.**  `K₀(ar)/K₀(r) → 1` as `r → 0⁺`, for `a > 0`. -/
theorem tendsto_kMoment_zero_mul_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r => kMoment 0 (a * r) / kMoment 0 r) (𝓝[>] 0) (𝓝 1) := by
  have h1 := WeilHigherDenominator.tendsto_kMoment_zero_mul_div_log ha
  have h2 := WeilHigherDenominator.tendsto_kMoment_zero_mul_div_log (c := 1) one_pos
  have hq := h1.div h2 (by norm_num)
  rw [show (-1 : ℝ) / -1 = 1 by norm_num] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_log_ne_zero_nhdsGT] with r hr
  simp only [Pi.div_apply, one_mul]
  rw [div_div_div_cancel_right₀ hr]

end RHTower.BesselKZero
