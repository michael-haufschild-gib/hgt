import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeBoundarySource
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # The exact first correction and locally uniform CDD boundary -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- The full finite-dimensional CDD correction after removing its zero-atom limit. -/
def egbFixedChargeAGibbsSpikeCDDCorrection (θ : ℝ) : ℝ :=
  -10 * Real.sinh θ + 3 * Real.arctan ((12 / 13 : ℝ) * Real.sinh θ) +
    12 * Real.arctan ((12 / 37 : ℝ) * Real.sinh θ)

/-- The literal boundary source has the flat zero-shell phase with coefficient two. -/
theorem egbFixedChargeAGibbsSpike_boundary_source_CDD_phase (θ : ℝ) :
    hausdorffCDDPhase egbFixedChargeAGibbsSpikeBoundarySource θ = 2 * Real.sinh θ := by
  change hausdorffCDDPhase (hausdorffAtomSource egbFixedChargeAGibbsSpikeBoundaryMass
    (⟨0, by constructor <;> norm_num⟩ : HausdorffSourceSpace)) θ = _
  rw [hausdorffCDDPhase_zero_atom]
  change 8 * (1 / 4 : ℝ) * Real.sinh θ = _
  ring

/-- The first correction is exact; no higher dimensional remainder is present. -/
theorem egbFixedChargeAGibbsSpike_CDD_boundary_decomposition (n : ℕ) (θ : ℝ) :
    egbFixedChargeAGibbsFullCollisionCDDPhase n 1 (egbFixedChargeAGibbsSpikeEnergy n) θ =
      2 * Real.sinh θ + ((2 : ℝ) ^ (n + 3))⁻¹ * egbFixedChargeAGibbsSpikeCDDCorrection θ := by
  rw [egbFixedChargeAGibbsSpike_full_CDD_phase]
  unfold egbFixedChargeAGibbsSpikeCDDCorrection
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hn]
  <;> ring

/-- Rescaling the phase error recovers the same analytic function at every dimension. -/
theorem egbFixedChargeAGibbsSpike_CDD_rescaled_error (n : ℕ) (θ : ℝ) :
    (2 : ℝ) ^ (n + 3) *
      (egbFixedChargeAGibbsFullCollisionCDDPhase n 1 (egbFixedChargeAGibbsSpikeEnergy n) θ -
        2 * Real.sinh θ) = egbFixedChargeAGibbsSpikeCDDCorrection θ := by
  rw [egbFixedChargeAGibbsSpike_CDD_boundary_decomposition]
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hn]
  <;> ring

/-- The dimensional correction is continuous on the whole real rapidity axis. -/
theorem egbFixedChargeAGibbsSpike_CDD_correction_continuous :
    Continuous egbFixedChargeAGibbsSpikeCDDCorrection := by
  unfold egbFixedChargeAGibbsSpikeCDDCorrection
  fun_prop

/-- The complete CDD phase converges to the endpoint contribution at every real rapidity. -/
theorem egbFixedChargeAGibbsSpike_CDD_tendsto_boundary (θ : ℝ) :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsFullCollisionCDDPhase n 1
      (egbFixedChargeAGibbsSpikeEnergy n) θ) atTop (nhds (2 * Real.sinh θ)) := by
  have hc : Tendsto (fun _ : ℕ => 2 * Real.sinh θ) atTop (nhds (2 * Real.sinh θ)) := tendsto_const_nhds
  have h := hc.add (egbFixedChargeAGibbsSpike_inverse_grid_tendsto_zero.mul_const
    (egbFixedChargeAGibbsSpikeCDDCorrection θ))
  simpa only [egbFixedChargeAGibbsSpike_CDD_boundary_decomposition, zero_mul, add_zero] using h

/-- Dimensional convergence holds locally uniformly, not merely pointwise. -/
theorem egbFixedChargeAGibbsSpike_CDD_tendstoLocallyUniformly :
    TendstoLocallyUniformly (fun (n : ℕ) (θ : ℝ) =>
      egbFixedChargeAGibbsFullCollisionCDDPhase n 1 (egbFixedChargeAGibbsSpikeEnergy n) θ)
      (fun θ => 2 * Real.sinh θ) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro θ
  have hb : Tendsto (fun p : ℕ × ℝ => 2 * Real.sinh p.2) (atTop ×ˢ nhds θ)
      (nhds (2 * Real.sinh θ)) := ((Real.continuous_sinh.tendsto θ).comp tendsto_snd).const_mul 2
  have hi : Tendsto (fun p : ℕ × ℝ => ((2 : ℝ) ^ (p.1 + 3))⁻¹)
      (atTop ×ˢ nhds θ) (nhds 0) := egbFixedChargeAGibbsSpike_inverse_grid_tendsto_zero.comp tendsto_fst
  have hc : Tendsto (fun p : ℕ × ℝ => egbFixedChargeAGibbsSpikeCDDCorrection p.2)
      (atTop ×ˢ nhds θ) (nhds (egbFixedChargeAGibbsSpikeCDDCorrection θ)) :=
    (egbFixedChargeAGibbsSpike_CDD_correction_continuous.tendsto θ).comp tendsto_snd
  have hp : Tendsto (fun p : ℕ × ℝ => egbFixedChargeAGibbsFullCollisionCDDPhase p.1 1
      (egbFixedChargeAGibbsSpikeEnergy p.1) p.2) (atTop ×ˢ nhds θ) (nhds (2 * Real.sinh θ)) := by
    simpa only [egbFixedChargeAGibbsSpike_CDD_boundary_decomposition, zero_mul, add_zero] using hb.add (hi.mul hc)
  exact (hb.prodMk_nhds hp).mono_right (nhds_le_uniformity _)

/-- Every closed bounded rapidity interval has uniform convergence to the boundary phase. -/
theorem egbFixedChargeAGibbsSpike_CDD_tendstoUniformlyOn_interval (T : ℝ) :
    TendstoUniformlyOn (fun (n : ℕ) (θ : ℝ) =>
      egbFixedChargeAGibbsFullCollisionCDDPhase n 1 (egbFixedChargeAGibbsSpikeEnergy n) θ)
      (fun θ => 2 * Real.sinh θ) atTop (Set.Icc (-|T|) |T|) := by
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    egbFixedChargeAGibbsSpike_CDD_tendstoLocallyUniformly.tendstoLocallyUniformlyOn

end
end GaloisForLFunctions.HTGeometry
