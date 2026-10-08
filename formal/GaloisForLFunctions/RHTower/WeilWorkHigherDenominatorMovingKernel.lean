import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionGeometry

/-!
# Fixed-mode limits along the actual inversion path

A moving positive scale is squeezed between two fixed scales. This identifies
each Fourier mode's limit; passing through the infinite series additionally
requires the uniform nonstationary-phase majorant.
-/

noncomputable section

open Set Filter Topology
open RHTower.BesselKZero

namespace RHTower.WeilHigherDenominator

theorem tendsto_kMoment_zero_variable_mul_div_log {c : ℝ → ℝ} {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀)) :
    Tendsto (fun y : ℝ => kMoment 0 (c y * y) / Real.log y) (𝓝[>] 0) (𝓝 (-1)) := by
  have hb : ∀ᶠ y : ℝ in 𝓝[>] 0, c y ∈ Ioo (c₀ / 2) (2 * c₀) :=
    hc.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have hl : ∀ᶠ y : ℝ in 𝓝[>] 0, Real.log y ≤ 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_le_atBot 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_kMoment_zero_mul_div_log (by positivity : 0 < c₀ / 2))
    (tendsto_kMoment_zero_mul_div_log (by positivity : 0 < 2 * c₀)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, hb, hl] with y hy hcy hlog
    apply div_le_div_of_nonpos_of_le hlog
    exact kMoment_zero_antitone (mul_pos (by positivity : 0 < c₀ / 2) hy)
      (mul_le_mul_of_nonneg_right hcy.1.le hy.le)
  · filter_upwards [self_mem_nhdsWithin, hb, hl] with y hy hcy hlog
    apply div_le_div_of_nonpos_of_le hlog
    exact kMoment_zero_antitone (mul_pos (lt_trans (by positivity : 0 < c₀ / 2) hcy.1) hy)
      (mul_le_mul_of_nonneg_right hcy.2.le hy.le)

theorem tendsto_inversion_scaledKLog {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    Tendsto (fun y : ℝ => scaledKLog (inversionBoundaryScale y) k y x)
      (𝓝[>] 0) (𝓝 (-1)) := by
  have hd : Continuous (fun y : ℝ => x ^ 2 + y ^ 2) := by fun_prop
  have hc : Continuous (fun y : ℝ => k * inversionBoundaryScale y x) :=
    continuous_const.mul (continuous_const.div hd fun y => (inversionBoundaryDenom_pos hx y).ne')
  have ht := tendsto_kMoment_zero_variable_mul_div_log
    (mul_pos hk (inversionBoundaryScale_pos hx 0))
    ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
  simpa only [scaledKLog, mul_right_comm] using ht

theorem tendsto_inversionBoundaryWeight {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => inversionBoundaryWeight y x) (𝓝[>] 0) (𝓝 x⁻¹) := by
  have hd : Continuous (fun y : ℝ => x ^ 2 + y ^ 2) := by fun_prop
  have hw : Continuous (fun y : ℝ => inversionBoundaryWeight y x) :=
    hd.rpow_const fun y => Or.inl (inversionBoundaryDenom_pos hx y).ne'
  have he : inversionBoundaryWeight 0 x = x⁻¹ := by
    rw [inversionBoundaryWeight, zero_pow (by decide : 2 ≠ 0), add_zero,
      Real.rpow_neg (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx.le]
  simpa only [he] using (hw.tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_inversion_weighted_scaledKLog {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    Tendsto (fun y : ℝ => inversionBoundaryWeight y x *
      scaledKLog (inversionBoundaryScale y) k y x) (𝓝[>] 0) (𝓝 (-x⁻¹)) := by
  simpa only [mul_neg_one] using (tendsto_inversionBoundaryWeight hx).mul
    (tendsto_inversion_scaledKLog hx hk)

end RHTower.WeilHigherDenominator
