import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShortMollifierKeepsItsLogarithmicScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Conductor geometry of tapered blocks

A sublinear taper has negligible relative width. On blocks above a fixed
multiple of `U/log U`, every supported height has logarithmic scale
`log U`. Dividing by the short mollifier's logarithmic length therefore
gives the conductor ratio `50/13`.
-/

open Filter Metric Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Every sublinear power is negligible relative to the block height. -/
theorem tendsto_taper_div_height {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l atTop) {ρ : ℝ} (hρ : ρ < 1) :
    Tendsto (fun i => a i ^ ρ / a i) l (𝓝 0) := by
  apply ((tendsto_rpow_neg_atTop (sub_pos.mpr hρ)).comp ha).congr'
  filter_upwards [ha.eventually_gt_atTop 0] with i hi
  rw [neg_sub, Real.rpow_sub hi, Real.rpow_one]

/-- Removing a sublinear taper leaves a height tending to infinity. -/
theorem tendsto_height_sub_taper {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l atTop) {ρ : ℝ} (hρ : ρ < 1) :
    Tendsto (fun i => a i - a i ^ ρ) l atTop := by
  have hsmall := (tendsto_taper_div_height ha hρ).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply Filter.tendsto_atTop.2
  intro M
  filter_upwards [ha.eventually_ge_atTop (2 * M), ha.eventually_gt_atTop 0,
    hsmall] with i hi hi0 hsi
  have hh := (div_lt_iff₀ hi0).mp hsi
  linarith only [hi, hh]

/-- Taper support has uniformly bounded length relative to a dyadic block. -/
theorem eventually_tapered_block_geometry {ι : Type*} {l : Filter ι} {a v : ι → ℝ}
    (ha : Tendsto a l atTop) {ρ : ℝ} (hρ : ρ < 1)
    (hv : ∀ᶠ i in l, a i ≤ v i ∧ v i ≤ 2 * a i) :
    ∀ᶠ i in l, 0 < a i ^ ρ ∧ a i / 2 ≤ a i - a i ^ ρ ∧
      v i + a i ^ ρ ≤ 3 * a i ∧
      (v i - a i + 2 * a i ^ ρ) / a i ≤ 2 := by
  filter_upwards [ha.eventually_gt_atTop 0, hv,
    (tendsto_taper_div_height ha hρ).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hi hvi hsi
  have hh := (div_lt_iff₀ hi).mp hsi
  refine ⟨Real.rpow_pos_of_pos hi _, by linarith only [hh],
    by linarith only [hvi.2, hh, hi], ?_⟩
  apply (div_le_iff₀ hi).mpr
  linarith only [hvi.2, hh]

/-- A logarithmic height band above `c U/log U` has the full upper-height scale. -/
theorem tendsto_log_height_div_log_of_logarithmic_band
    {ι : Type*} {l : Filter ι} {U t : ι → ℝ} (hU : Tendsto U l atTop)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hband : ∀ᶠ i in l, c * U i / Real.log (U i) ≤ t i ∧ t i ≤ C * U i) :
    Tendsto (fun i => Real.log (t i) / Real.log (U i)) l (𝓝 1) := by
  have hL := Real.tendsto_log_atTop.comp hU
  have hll : Tendsto (fun i => Real.log (Real.log (U i)) / Real.log (U i)) l (𝓝 0) := by
    have hh := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa only [one_mul, add_zero, pow_one, Function.comp_def] using hh.comp hL
  have hlo : Tendsto (fun i => 1 + Real.log c / Real.log (U i) -
      Real.log (Real.log (U i)) / Real.log (U i)) l (𝓝 1) := by
    simpa only [add_zero, sub_zero] using
      ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hL)).sub hll)
  have hhi : Tendsto (fun i => 1 + Real.log C / Real.log (U i)) l (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hL)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hlo.eventually (Metric.ball_mem_nhds 1 hε),
    hhi.eventually (Metric.ball_mem_nhds 1 hε), hband,
    hU.eventually_gt_atTop 1] with i hli hri hbi hUi
  have hUi0 : 0 < U i := zero_lt_one.trans hUi
  have hLi : 0 < Real.log (U i) := Real.log_pos hUi
  have ht : 0 < t i := (div_pos (mul_pos hc hUi0) hLi).trans_le hbi.1
  have hleft := div_le_div_of_nonneg_right
    (Real.log_le_log (div_pos (mul_pos hc hUi0) hLi) hbi.1) hLi.le
  have hright := div_le_div_of_nonneg_right (Real.log_le_log ht hbi.2) hLi.le
  rw [Real.log_div (mul_pos hc hUi0).ne' hLi.ne', Real.log_mul hc.ne' hUi0.ne'] at hleft
  rw [Real.log_mul hC.ne' hUi0.ne'] at hright
  have heleft : (Real.log c + Real.log (U i) - Real.log (Real.log (U i))) / Real.log (U i) =
      1 + Real.log c / Real.log (U i) - Real.log (Real.log (U i)) / Real.log (U i) := by
    field_simp [hLi.ne'] <;> ring
  have heright : (Real.log C + Real.log (U i)) / Real.log (U i) =
      1 + Real.log C / Real.log (U i) := by field_simp [hLi.ne'] <;> ring
  rw [heleft] at hleft
  rw [heright] at hright
  change dist (1 + Real.log c / Real.log (U i) - Real.log (Real.log (U i)) / Real.log (U i)) 1 < ε at hli
  change dist (1 + Real.log C / Real.log (U i)) 1 < ε at hri
  rw [Real.dist_eq] at hli hri ⊢
  exact abs_lt.mpr ⟨by linarith only [(abs_lt.mp hli).1, hleft],
    by linarith only [(abs_lt.mp hri).2, hright]⟩

/-- A fixed conductor normalization does not change a logarithmic height limit. -/
theorem tendsto_log_conductor_div_short_length
    {ι : Type*} {l : Filter ι} {U t : ι → ℝ} (hU : Tendsto U l atTop)
    (ht : ∀ᶠ i in l, 0 < t i)
    (hscale : Tendsto (fun i => Real.log (t i) / Real.log (U i)) l (𝓝 1)) :
    Tendsto (fun i => Real.log (t i / (2 * Real.pi)) /
      Real.log (shortLevinsonCutoff (U i))) l (𝓝 (50 / 13 : ℝ)) := by
  have hL := Real.tendsto_log_atTop.comp hU
  have hc : Tendsto (fun i => Real.log (2 * Real.pi) / Real.log (U i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hh := (hscale.sub hc).div (tendsto_log_shortLevinsonCutoff_div_log.comp hU)
    (by norm_num : (13 / 50 : ℝ) ≠ 0)
  norm_num only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [ht, hU.eventually_gt_atTop 1] with i hti hUi
  rw [Real.log_div hti.ne' (by positivity : (2 * Real.pi) ≠ 0)]
  field_simp [(Real.log_pos hUi).ne'] <;> ring

/-- Both ends of a high block's taper have the selected normalized conductor. -/
theorem tendsto_tapered_block_conductor_endpoints
    {ι : Type*} {l : Filter ι} {U a v : ι → ℝ}
    (hU : Tendsto U l atTop) (ha : Tendsto a l atTop)
    {ρ δ : ℝ} (hρ : ρ < 1) (hδ : 0 < δ)
    (hblock : ∀ᶠ i in l, a i ≤ v i ∧ v i ≤ 2 * a i ∧ v i ≤ U i ∧
      δ * U i / Real.log (U i) ≤ a i) :
    Tendsto (fun i => Real.log ((a i - a i ^ ρ) / (2 * Real.pi)) /
      Real.log (shortLevinsonCutoff (U i))) l (𝓝 (50 / 13 : ℝ)) ∧
    Tendsto (fun i => Real.log ((v i + a i ^ ρ) / (2 * Real.pi)) /
      Real.log (shortLevinsonCutoff (U i))) l (𝓝 (50 / 13 : ℝ)) := by
  have hg := eventually_tapered_block_geometry ha hρ
    (hblock.mono (fun _ hi => ⟨hi.1, hi.2.1⟩))
  have hb : ∀ᶠ i in l,
      (δ / 2 * U i / Real.log (U i) ≤ a i - a i ^ ρ ∧ a i - a i ^ ρ ≤ 3 * U i) ∧
      (δ / 2 * U i / Real.log (U i) ≤ v i + a i ^ ρ ∧ v i + a i ^ ρ ≤ 3 * U i) := by
    filter_upwards [hblock, hg, hU.eventually_gt_atTop 1] with i hi hgi hUi
    have hUi0 : 0 < U i := zero_lt_one.trans hUi
    have hLi : 0 < Real.log (U i) := Real.log_pos hUi
    have hδi : 0 ≤ δ * U i / Real.log (U i) := by positivity
    have he : δ / 2 * U i / Real.log (U i) = (δ * U i / Real.log (U i)) / 2 := by ring
    rw [he]
    exact ⟨⟨by linarith only [hi.2.2.2, hgi.2.1],
      by linarith only [hi.1, hi.2.2.1, hgi.1, hUi0]⟩,
      ⟨by linarith only [hi.1, hi.2.2.2, hgi.1, hδi],
      by linarith only [hgi.2.2.1, hi.1, hi.2.2.1]⟩⟩
  have hpa := (tendsto_height_sub_taper ha hρ).eventually_gt_atTop 0
  have hpb : ∀ᶠ i in l, 0 < v i + a i ^ ρ := by
    filter_upwards [ha.eventually_gt_atTop 0, hblock] with i hai hi
    exact add_pos (hai.trans_le hi.1) (Real.rpow_pos_of_pos hai _)
  exact ⟨tendsto_log_conductor_div_short_length hU hpa
      (tendsto_log_height_div_log_of_logarithmic_band hU (by positivity : 0 < δ / 2)
        (by norm_num : (0 : ℝ) < 3) (hb.mono (fun _ hi => hi.1))),
    tendsto_log_conductor_div_short_length hU hpb
      (tendsto_log_height_div_log_of_logarithmic_band hU (by positivity : 0 < δ / 2)
        (by norm_num : (0 : ℝ) < 3) (hb.mono (fun _ hi => hi.2)))⟩

/-- Above the low-block cutoff, the mollifier is strictly below the local square root. -/
theorem shortLevinsonCutoff_le_block_power {U a : ℝ} (hU : 0 < U)
    (ha : U ^ (53 / 100 : ℝ) ≤ a) :
    (shortLevinsonCutoff U : ℝ) ≤ a ^ (26 / 53 : ℝ) := by
  calc
    _ ≤ U ^ (13 / 50 : ℝ) := Nat.floor_le (Real.rpow_nonneg hU.le _)
    _ = (U ^ (53 / 100 : ℝ)) ^ (26 / 53 : ℝ) := by
      rw [← Real.rpow_mul hU.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hU.le _) ha (by norm_num)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
