import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFrozenMainJetsHaveTheirScalarLimits
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTaperedBlocksKeepTheirConductorScale
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheGateDisplacementsHaveOneNormalizedLimit

/-!
# The sharp main term on high detector blocks

The same upper-height cutoff and every admissible gate displacement give
the scalar `c(13/50)` on blocks above `δ U/log U`. The taper mass differs
from the block length by a sublinear edge, leaving a coefficient below
`18/5` with arbitrary additive slack relative to block height.
-/

open Filter MeasureTheory Polynomial Set Topology
open RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The literal matched main term has the sharp scalar along every admissible high-block selection. -/
theorem tendsto_high_detector_main_error
    {ι : Type*} {l : Filter ι} {U a v d : ι → ℝ}
    (hU : Tendsto U l atTop) (ha : Tendsto a l atTop)
    {ρ δ : ℝ} (hρ : ρ < 1) (hδ : 0 < δ)
    (hblock : ∀ᶠ i in l, a i ≤ v i ∧ v i ≤ 2 * a i ∧ v i ≤ U i ∧
      δ * U i / Real.log (U i) ≤ a i)
    (hgate : ∀ᶠ i in l, 13 / 10 ≤ d i * Real.log (U i) ∧
      d i * Real.log (U i - 1) ≤ 13 / 10) :
    Tendsto (fun i => (detectorThreeMomentMain (a i) (v i) (a i ^ ρ)
      (shortLevinsonCutoff (U i)) (linearDetectorWeights (shortLevinsonCutoff (U i)) (d i))
      (d i) (1 / Real.log (U i)) -
      (∫ t, blockWindow (a i) (v i) (a i ^ ρ) t) *
        threeProfileDetectorScalar (13 / 50) (13 / 10)) / a i) l (𝓝 0) := by
  have hn : Tendsto (fun i => shortLevinsonCutoff (U i)) l atTop := tendsto_shortLevinsonCutoff.comp hU
  have hu := tendsto_gate_normalized_displacement hU (by norm_num : (0 : ℝ) ≤ 13 / 10) hgate
  have hlam : Tendsto (fun i => (1 / Real.log (U i)) *
      Real.log (shortLevinsonCutoff (U i))) l (𝓝 (13 / 50 : ℝ)) := by
    simpa only [Function.comp_def, one_div, mul_comm, ← div_eq_mul_inv] using
      tendsto_log_shortLevinsonCutoff_div_log.comp hU
  obtain ⟨hca, hcb⟩ := tendsto_tapered_block_conductor_endpoints hU ha hρ hδ hblock
  have hca' : Tendsto (fun i => Real.log ((a i - a i ^ ρ) / (2 * Real.pi)) /
      Real.log (shortLevinsonCutoff (U i))) l (𝓝 (1 / (13 / 50 : ℝ))) := by norm_num; exact hca
  have hcb' : Tendsto (fun i => Real.log ((v i + a i ^ ρ) / (2 * Real.pi)) /
      Real.log (shortLevinsonCutoff (U i))) l (𝓝 (1 / (13 / 50 : ℝ))) := by norm_num; exact hcb
  have hg := eventually_tapered_block_geometry ha hρ
    (hblock.mono (fun _ hi => ⟨hi.1, hi.2.1⟩))
  have hgeom : ∀ᶠ i in l, 0 < a i ^ ρ ∧ a i ≤ v i ∧ 0 < a i ∧
      (v i - a i + 2 * a i ^ ρ) / a i ≤ 2 := by
    filter_upwards [hg, hblock, ha.eventually_gt_atTop 0] with i hgi hi hai
    exact ⟨hgi.1, hi.1, hai, hgi.2.2.2⟩
  exact tendsto_detectorThreeMomentMain_error hn (tendsto_height_sub_taper ha hρ)
    (by norm_num : (0 : ℝ) < 13 / 50) (by norm_num : (0 : ℝ) < 13 / 10)
    hu hlam (by norm_num : (0 : ℝ) ≤ 2) hca' hcb' hgeom

/-- The sharp scalar and negligible taper edges bound the actual main term by block length. -/
theorem eventually_high_detector_main_le
    {ι : Type*} {l : Filter ι} {U a v d : ι → ℝ}
    (hU : Tendsto U l atTop) (ha : Tendsto a l atTop)
    {ρ δ : ℝ} (hρ : ρ < 1) (hδ : 0 < δ)
    (hblock : ∀ᶠ i in l, a i ≤ v i ∧ v i ≤ 2 * a i ∧ v i ≤ U i ∧
      δ * U i / Real.log (U i) ≤ a i)
    (hgate : ∀ᶠ i in l, 13 / 10 ≤ d i * Real.log (U i) ∧
      d i * Real.log (U i - 1) ≤ 13 / 10) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, detectorThreeMomentMain (a i) (v i) (a i ^ ρ)
      (shortLevinsonCutoff (U i)) (linearDetectorWeights (shortLevinsonCutoff (U i)) (d i))
      (d i) (1 / Real.log (U i)) ≤ (18 / 5) * (v i - a i) + ε * a i := by
  have he := (tendsto_high_detector_main_error hU ha hρ hδ hblock hgate).eventually
    (Iio_mem_nhds (half_pos hε))
  have ht := (tendsto_taper_div_height ha hρ).eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < ε * (5 / 72)))
  filter_upwards [he, ht, hblock, ha.eventually_gt_atTop 0] with i hei hti hi hai
  have hmain := (div_lt_iff₀ hai).mp hei
  have hedge := (div_lt_iff₀ hai).mp hti
  have hmass := integral_blockWindow_le (Real.rpow_pos_of_pos hai ρ) hi.1
  have hscalar := mul_le_mul_of_nonneg_left threeProfileDetectorScalar_selected_lt.le
    (integral_blockWindow_nonneg (a i) (v i) (a i ^ ρ))
  nlinarith only [hmain, hedge, hmass, hscalar]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
