import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheMainJetsStayBoundedAtBoundedConductor
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheHighDetectorMainHasItsSharpScalar
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheGateBlocksMeetTheMomentHypotheses
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTaperBoundsTheActualDetectorBlock

/-!
# Actual matched-detector bounds above the low-height split

The twisted-moment remainder and taper domination turn the main-term
bounds into bounds for the literal interval energy. Intermediate blocks
have linear-size energy; blocks above `δ U/log U` have coefficient `18/5`
with arbitrary additive slack relative to block height.
-/

open Asymptotics Filter MeasureTheory Set Topology
open RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Every admissible family of large blocks has uniformly linear matched-detector energy. -/
theorem exists_eventually_matchedDetectorBlockEnergy_le
    {ι : Type*} {l : Filter ι} {U a v d : ι → ℝ} (hU : Tendsto U l atTop)
    (hblock : ∀ᶠ i in l, U i ^ (53 / 100 : ℝ) ≤ a i ∧ a i ≤ v i ∧
      v i ≤ 2 * a i ∧ v i ≤ U i)
    (hgate : ∀ᶠ i in l, 13 / 10 ≤ d i * Real.log (U i) ∧
      d i * Real.log (U i - 1) ≤ 13 / 10) :
    ∃ C > 0, ∀ᶠ i in l, matchedDetectorBlockEnergy (shortLevinsonCutoff (U i))
      (d i) (1 / Real.log (U i)) (a i) (v i) ≤ C * a i := by
  obtain ⟨ρ, r, E, hρ0, hρ1, hr, hE, herr⟩ := exists_linearDetector_main_remainder_bound
    (by norm_num : (0 : ℝ) ≤ 26 / 53) (by norm_num : (26 / 53 : ℝ) < 1 / 2)
  have ha := tendsto_gate_block_height hU (hblock.mono (fun _ hi => hi.1))
  have hn := tendsto_shortLevinsonCutoff.comp hU
  have hp := tendsto_height_sub_taper ha hρ1
  have hg := eventually_tapered_block_geometry ha hρ1
    (hblock.mono (fun _ hi => ⟨hi.2.1, hi.2.2.1⟩))
  have hgeom : ∀ᶠ i in l, 0 < a i ^ ρ ∧ a i ≤ v i ∧ 0 < a i ∧
      (v i - a i + 2 * a i ^ ρ) / a i ≤ 2 := by
    filter_upwards [hg, hblock, ha.eventually_gt_atTop 0] with i hgi hi hai
    exact ⟨hgi.1, hi.2.1, hai, hgi.2.2.2⟩
  have hu := tendsto_gate_normalized_displacement hU (by norm_num : (0 : ℝ) ≤ 13 / 10) hgate
  have hlam : Tendsto (fun i => (1 / Real.log (U i)) *
      Real.log (shortLevinsonCutoff (U i))) l (𝓝 (13 / 50 : ℝ)) := by
    simpa only [one_div, mul_comm, ← div_eq_mul_inv] using
      tendsto_log_shortLevinsonCutoff_div_log.comp hU
  have hmain := isBigO_detectorThreeMomentMain hn hp hu (by norm_num) hlam
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 10) hgeom
    (eventually_gate_block_conductor_bounded hU hρ1 hblock)
  obtain ⟨D, hD⟩ := hmain.bound
  have hvalid := eventually_gate_block_moment_hypotheses hU
    (hblock.mono (fun _ hi => hi.1)) hgate hr
  refine ⟨|D| + E + 1, by positivity, ?_⟩
  filter_upwards [hD, hvalid, hblock, hgeom, ha.eventually herr,
    ha.eventually_ge_atTop 1, hp.eventually_ge_atTop 1] with i hDi hvi hi hgi hei hai hpi
  have he := hei (v i) (d i) (1 / Real.log (U i)) (shortLevinsonCutoff (U i))
    hi.2.1 hi.2.2.1 hvi.1 hvi.2.1 hvi.2.2.1 hvi.2.2.2.1
    hvi.2.2.2.2.1 hvi.2.2.2.2.2.1 hvi.2.2.2.2.2.2
  have hw := matchedDetectorBlockEnergy_le_taper hgi.1 hpi hi.2.1
    (shortLevinsonCutoff (U i)) (d i) (1 / Real.log (U i))
  have hpow : a i ^ (7 / 8 : ℝ) ≤ a i := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hai (by norm_num : (7 / 8 : ℝ) ≤ 1)
  have hep := mul_le_mul_of_nonneg_left hpow hE.le
  have hDa := mul_le_mul_of_nonneg_right (le_abs_self D) (zero_lt_one.trans_le hai).le
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (zero_lt_one.trans_le hai).le] at hDi
  have hm := le_abs_self (detectorThreeMomentMain (a i) (v i) (a i ^ ρ)
    (shortLevinsonCutoff (U i)) (linearDetectorWeights (shortLevinsonCutoff (U i)) (d i))
    (d i) (1 / Real.log (U i)))
  linarith only [hw, (abs_le.mp he).2, hm, hDi, hDa, hep, hai]

/-- On high blocks the actual interval energy has the sharp coefficient and vanishing relative error. -/
theorem eventually_matchedDetectorBlockEnergy_high_le
    {ι : Type*} {l : Filter ι} {U a v d : ι → ℝ} (hU : Tendsto U l atTop)
    (hblock : ∀ᶠ i in l, U i ^ (53 / 100 : ℝ) ≤ a i ∧ a i ≤ v i ∧
      v i ≤ 2 * a i ∧ v i ≤ U i)
    (hgate : ∀ᶠ i in l, 13 / 10 ≤ d i * Real.log (U i) ∧
      d i * Real.log (U i - 1) ≤ 13 / 10) {δ : ℝ} (hδ : 0 < δ)
    (hhigh : ∀ᶠ i in l, δ * U i / Real.log (U i) ≤ a i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, matchedDetectorBlockEnergy (shortLevinsonCutoff (U i))
      (d i) (1 / Real.log (U i)) (a i) (v i) ≤ (18 / 5) * (v i - a i) + ε * a i := by
  obtain ⟨ρ, r, E, hρ0, hρ1, hr, hE, herr⟩ := exists_linearDetector_main_remainder_bound
    (by norm_num : (0 : ℝ) ≤ 26 / 53) (by norm_num : (26 / 53 : ℝ) < 1 / 2)
  have ha := tendsto_gate_block_height hU (hblock.mono (fun _ hi => hi.1))
  have hp := tendsto_height_sub_taper ha hρ1
  have hfull : ∀ᶠ i in l, a i ≤ v i ∧ v i ≤ 2 * a i ∧ v i ≤ U i ∧
      δ * U i / Real.log (U i) ≤ a i := by
    filter_upwards [hblock, hhigh] with i hi hhi
    exact ⟨hi.2.1, hi.2.2.1, hi.2.2.2, hhi⟩
  have hmain := eventually_high_detector_main_le hU ha hρ1 hδ hfull hgate (half_pos hε)
  have hvalid := eventually_gate_block_moment_hypotheses hU
    (hblock.mono (fun _ hi => hi.1)) hgate hr
  have he0 := (tendsto_taper_div_height ha (by norm_num : (7 / 8 : ℝ) < 1)).const_mul E
  simp only [mul_zero] at he0
  filter_upwards [hmain, hvalid, hblock, ha.eventually herr, ha.eventually_gt_atTop 0,
    hp.eventually_ge_atTop 1, he0.eventually (Iio_mem_nhds (half_pos hε))]
    with i hmi hvi hi hei hai hpi hsi
  have he := hei (v i) (d i) (1 / Real.log (U i)) (shortLevinsonCutoff (U i))
    hi.2.1 hi.2.2.1 hvi.1 hvi.2.1 hvi.2.2.1 hvi.2.2.2.1
    hvi.2.2.2.2.1 hvi.2.2.2.2.2.1 hvi.2.2.2.2.2.2
  have hw := matchedDetectorBlockEnergy_le_taper (Real.rpow_pos_of_pos hai ρ) hpi hi.2.1
    (shortLevinsonCutoff (U i)) (d i) (1 / Real.log (U i))
  have hs : E * a i ^ (7 / 8 : ℝ) < (ε / 2) * a i := by
    apply (div_lt_iff₀ hai).mp
    simpa only [mul_div_assoc] using hsi
  linarith only [hw, (abs_le.mp he).2, hmi, hs]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
