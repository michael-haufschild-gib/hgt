import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTaperedBlocksKeepTheirConductorScale
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheGateDisplacementsHaveOneNormalizedLimit
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheChiWeightJetsHaveTheirConductorLimits
import GaloisForLFunctions.RHTower.HighBlockAsymptotics

/-!
# Uniform geometry above the low-height split

Above `U^(53/100)`, the cutoff is at most the local power `a^(26/53)`.
Every gate displacement meets the lower displacement bound of the
moment estimate. The whole taper has bounded normalized conductor,
including intermediate blocks below `U/log U`.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Every height above the low-block split tends to infinity. -/
theorem tendsto_gate_block_height {ι : Type*} {l : Filter ι} {U a : ι → ℝ}
    (hU : Tendsto U l atTop) (ha : ∀ᶠ i in l, U i ^ (53 / 100 : ℝ) ≤ a i) :
    Tendsto a l atTop := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 53 / 100)).comp hU
  apply Filter.tendsto_atTop.2
  intro M
  filter_upwards [hp.eventually_ge_atTop M, ha] with i hi hai
  exact hi.trans hai

/-- All supported heights have conductor rate at most ten above the low-block split. -/
theorem eventually_gate_block_conductor_bounded
    {ι : Type*} {l : Filter ι} {U a v : ι → ℝ} (hU : Tendsto U l atTop)
    {ρ : ℝ} (hρ : ρ < 1)
    (hblock : ∀ᶠ i in l, U i ^ (53 / 100 : ℝ) ≤ a i ∧ a i ≤ v i ∧
      v i ≤ 2 * a i ∧ v i ≤ U i) :
    ∀ᶠ i in l, ∀ t ∈ Icc (a i - a i ^ ρ) (v i + a i ^ ρ),
      ‖scaledChiConductorRate (Real.log (shortLevinsonCutoff (U i))) t‖ ≤ 10 := by
  have ha := tendsto_gate_block_height hU (hblock.mono (fun _ hi => hi.1))
  have hg := eventually_tapered_block_geometry ha hρ
    (hblock.mono (fun _ hi => ⟨hi.2.1, hi.2.2.1⟩))
  have hratio := (tendsto_log_shortLevinsonCutoff_div_log.comp hU).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 5 : ℝ) < 13 / 50))
  filter_upwards [hblock, hg, hratio, hU.eventually_gt_atTop 1,
    (tendsto_height_sub_taper ha hρ).eventually_ge_atTop (2 * Real.pi)]
    with i hi hgi hri hUi hpi
  intro t ht
  have hUi0 : 0 < U i := zero_lt_one.trans hUi
  have hLU : 0 < Real.log (U i) := Real.log_pos hUi
  have hLlo := (lt_div_iff₀ hLU).mp hri
  have hL : 0 < Real.log (shortLevinsonCutoff (U i) : ℝ) := by linarith only [hLlo, hLU]
  have htpi : 2 * Real.pi ≤ t := hpi.trans ht.1
  have ht0 : 0 < t := (by positivity : (0 : ℝ) < 2 * Real.pi).trans_le htpi
  have htU : t ≤ 3 * U i := by linarith only [ht.2, hgi.2.2.1, hi.2.1, hi.2.2.2]
  have hratioU : t / (2 * Real.pi) ≤ U i := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    calc
      t ≤ 3 * U i := htU
      _ ≤ (2 * Real.pi) * U i := mul_le_mul_of_nonneg_right
        (by linarith only [Real.pi_gt_three]) hUi0.le
      _ = _ := mul_comm _ _
  have hlog0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr htpi)
  have hlogU := Real.log_le_log (by positivity : 0 < t / (2 * Real.pi)) hratioU
  have he : scaledChiConductorRate (Real.log (shortLevinsonCutoff (U i))) t =
      ((2 * Real.log (t / (2 * Real.pi)) / Real.log (shortLevinsonCutoff (U i)) : ℝ) : ℂ) := by
    simp only [scaledChiConductorRate, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hL).mpr
  linarith only [hlogU, hLlo]

/-- The actual upper-height mollifier satisfies every local moment hypothesis on all large blocks. -/
theorem eventually_gate_block_moment_hypotheses
    {ι : Type*} {l : Filter ι} {U a d : ι → ℝ} (hU : Tendsto U l atTop)
    (ha : ∀ᶠ i in l, U i ^ (53 / 100 : ℝ) ≤ a i)
    (hgate : ∀ᶠ i in l, 13 / 10 ≤ d i * Real.log (U i) ∧
      d i * Real.log (U i - 1) ≤ 13 / 10) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in l, 1 / a i ≤ d i ∧ d i ≤ min r (1 / 40) ∧
      1 < shortLevinsonCutoff (U i) ∧
      (shortLevinsonCutoff (U i) : ℝ) ≤ a i ^ (26 / 53 : ℝ) ∧
      0 ≤ 1 / Real.log (U i) ∧ 1 / Real.log (U i) ≤ 1 ∧
      (1 / Real.log (U i)) * Real.log (shortLevinsonCutoff (U i)) ≤ 1 := by
  have hsmall := (RHTower.tendsto_const_mul_rpow_neg_mul_log_pow 1 (53 / 100)
    (by norm_num) 1).comp hU
  have hsmall' : ∀ᶠ i in l, Real.log (U i) / U i ^ (53 / 100 : ℝ) ≤ 13 / 10 := by
    filter_upwards [hsmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 13 / 10)),
      hU.eventually_gt_atTop 0] with i hi hUi
    simpa only [Function.comp_def, one_mul, pow_one, Real.rpow_neg hUi.le, div_eq_mul_inv, mul_comm] using hi.le
  have hd := tendsto_gate_displacement_zero hU (by norm_num : (0 : ℝ) ≤ 13 / 10) hgate
  have hL := Real.tendsto_log_atTop.comp hU
  have hratio := (tendsto_log_shortLevinsonCutoff_div_log.comp hU).eventually
    (Iio_mem_nhds (by norm_num : (13 / 50 : ℝ) < 1))
  filter_upwards [ha, hgate, hsmall', hU.eventually_gt_atTop 1, hL.eventually_ge_atTop 1,
    hd.eventually (Iio_mem_nhds (lt_min hr (by norm_num))), hratio,
    (tendsto_shortLevinsonCutoff.comp hU).eventually_ge_atTop 2]
    with i hai hgi hsi hUi hLi hdi hri hni
  change 2 ≤ shortLevinsonCutoff (U i) at hni
  have hUi0 : 0 < U i := zero_lt_one.trans hUi
  have hLU : 0 < Real.log (U i) := Real.log_pos hUi
  have hp : 0 < U i ^ (53 / 100 : ℝ) := Real.rpow_pos_of_pos hUi0 _
  have hai0 : 0 < a i := hp.trans_le hai
  have hpow := (div_le_iff₀ hp).mp hsi
  have hlogA : Real.log (U i) ≤ (13 / 10) * a i :=
    hpow.trans (mul_le_mul_of_nonneg_left hai (by norm_num))
  have hlow : 1 / a i ≤ d i := by
    calc
      1 / a i ≤ (13 / 10) / Real.log (U i) :=
        (div_le_div_iff₀ hai0 hLU).mpr (by simpa only [one_mul] using hlogA)
      _ ≤ d i := (div_le_iff₀ hLU).mpr hgi.1
  refine ⟨hlow, hdi.le, by omega, shortLevinsonCutoff_le_block_power hUi0 hai,
    (one_div_pos.mpr hLU).le, (one_div_le_one_div_of_le zero_lt_one hLi).trans_eq (by norm_num), ?_⟩
  simpa only [Function.comp_def, one_div, mul_comm, ← div_eq_mul_inv] using hri.le

end GaloisForLFunctions.MultiscaleMollifiedZetaField
