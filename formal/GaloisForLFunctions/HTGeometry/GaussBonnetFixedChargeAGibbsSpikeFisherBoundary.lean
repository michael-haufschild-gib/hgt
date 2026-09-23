import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeRescaledSource
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeFisher

/-! # Fisher discontinuity at zero and its positive-source explanation -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- The actual three positive-time observations entering the temporal Fisher scalar. -/
def egbFixedChargeAGibbsSpikeFisherMomentPath (n m : ℕ) : ℝ × ℝ × ℝ :=
  (egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsSpikeEnergy n),
    egbFixedChargeAGibbsCollisionExcess n (m + 2) 1 (egbFixedChargeAGibbsSpikeEnergy n),
    egbFixedChargeAGibbsCollisionExcess n (m + 3) 1 (egbFixedChargeAGibbsSpikeEnergy n))

/-- The existing pure-state normalization map on its three real input values. -/
def egbFixedChargeAGibbsSpikeFisherBoundaryMap (v : ℝ × ℝ × ℝ) : ℝ :=
  _root_.HTGeometry.pureStateQuantumFisherValue v.1 v.2.1 v.2.2

/-- Fisher geometry of the literal rescaled positive source. -/
def egbFixedChargeAGibbsSpikeRescaledSourceFisher (m : ℕ) : ℝ :=
  _root_.HTGeometry.pureStateQuantumFisherValue
    (hausdorffMoment (egbFixedChargeAGibbsSpikeRescaledSource m) 0)
    (hausdorffMoment (egbFixedChargeAGibbsSpikeRescaledSource m) 1)
    (hausdorffMoment (egbFixedChargeAGibbsSpikeRescaledSource m) 2)

private theorem fisher_scale (s a b c : ℝ) (hs : s ≠ 0) :
    _root_.HTGeometry.pureStateQuantumFisherValue (s * a) (s * b) (s * c) =
      _root_.HTGeometry.pureStateQuantumFisherValue a b c := by
  unfold _root_.HTGeometry.pureStateQuantumFisherValue _root_.HTGeometry.projectiveQuantumTangentValue
  by_cases ha : a = 0
  · simp [ha]
  · field_simp [hs, ha]
    <;> ring

/-- All three actual inputs tend jointly to zero for every fixed observation offset. -/
theorem egbFixedChargeAGibbsSpike_fisher_inputs_tendsto_zero (m : ℕ) :
    Tendsto (fun n => egbFixedChargeAGibbsSpikeFisherMomentPath n m) atTop (nhds (0, 0, 0)) := by
  exact (egbFixedChargeAGibbsSpike_positive_collision_tendsto_zero m).prodMk_nhds
    ((egbFixedChargeAGibbsSpike_positive_collision_tendsto_zero (m + 1)).prodMk_nhds
      (egbFixedChargeAGibbsSpike_positive_collision_tendsto_zero (m + 2)))

/-- The same normalization map reads a fixed positive value along each shrinking moment path. -/
theorem egbFixedChargeAGibbsSpike_fisher_boundary_map_path (n m : ℕ) :
    egbFixedChargeAGibbsSpikeFisherBoundaryMap (egbFixedChargeAGibbsSpikeFisherMomentPath n m) =
      (25 / 36 : ℝ) * (1 / 16 : ℝ) ^ (m + 1) / (1 + (1 / 16 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
  exact egbFixedChargeAGibbsSpike_fisher_formula n m

/-- The dimensional Fisher limit is strictly positive even though every input vanishes. -/
theorem egbFixedChargeAGibbsSpike_fisher_boundary_limit (m : ℕ) :
    Tendsto (fun n => egbFixedChargeAGibbsSpikeFisherBoundaryMap (egbFixedChargeAGibbsSpikeFisherMomentPath n m))
      atTop (nhds ((25 / 36 : ℝ) * (1 / 16 : ℝ) ^ (m + 1) / (1 + (1 / 16 : ℝ) ^ (m + 1)) ^ (2 : ℕ))) ∧
    0 < (25 / 36 : ℝ) * (1 / 16 : ℝ) ^ (m + 1) / (1 + (1 / 16 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
  constructor
  · simpa only [egbFixedChargeAGibbsSpike_fisher_boundary_map_path] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (25 / 36 : ℝ) * (1 / 16 : ℝ) ^ (m + 1) / (1 + (1 / 16 : ℝ) ^ (m + 1)) ^ (2 : ℕ)) atTop (nhds _))
  · positivity

/-- The established pure-state normalization map is discontinuous at its zero-input convention. -/
theorem egbFixedChargeAGibbsSpike_fisher_not_continuousAt_zero :
    ¬ ContinuousAt egbFixedChargeAGibbsSpikeFisherBoundaryMap (0, 0, 0) := by
  intro h
  have hz : Tendsto (fun n => egbFixedChargeAGibbsSpikeFisherBoundaryMap
      (egbFixedChargeAGibbsSpikeFisherMomentPath n 0)) atTop (nhds 0) := by
    have hzero : egbFixedChargeAGibbsSpikeFisherBoundaryMap (0, 0, 0) = 0 := by
      simp [egbFixedChargeAGibbsSpikeFisherBoundaryMap,
        _root_.HTGeometry.pureStateQuantumFisherValue, _root_.HTGeometry.projectiveQuantumTangentValue]
    have hc := h.tendsto.comp (egbFixedChargeAGibbsSpike_fisher_inputs_tendsto_zero 0)
    change Tendsto (fun n => egbFixedChargeAGibbsSpikeFisherBoundaryMap
      (egbFixedChargeAGibbsSpikeFisherMomentPath n 0)) atTop
      (nhds (egbFixedChargeAGibbsSpikeFisherBoundaryMap (0, 0, 0))) at hc
    rw [hzero] at hc
    exact hc
  have he := tendsto_nhds_unique hz (egbFixedChargeAGibbsSpike_fisher_boundary_limit 0).1
  norm_num at he

/-- The literal rescaled positive source has exactly the Fisher geometry of every finite-dimensional state. -/
theorem egbFixedChargeAGibbsSpike_rescaled_source_fisher_eq (n m : ℕ) :
    egbFixedChargeAGibbsSpikeRescaledSourceFisher m =
      egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsSpikeEnergy n) := by
  unfold egbFixedChargeAGibbsSpikeRescaledSourceFisher
  rw [egbFixedChargeAGibbsSpike_rescaled_source_moment n m 0,
    egbFixedChargeAGibbsSpike_rescaled_source_moment n m 1,
    egbFixedChargeAGibbsSpike_rescaled_source_moment n m 2]
  simp only [zero_add, Nat.add_comm 1 m, Nat.add_comm 2 m]
  exact fisher_scale _ _ _ _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))

/-- The nonzero source recovered by rescaling supplies the exact limiting Fisher value. -/
theorem egbFixedChargeAGibbsSpike_rescaled_source_fisher_formula (m : ℕ) :
    egbFixedChargeAGibbsSpikeRescaledSourceFisher m =
      (25 / 36 : ℝ) * (1 / 16 : ℝ) ^ (m + 1) / (1 + (1 / 16 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
  rw [egbFixedChargeAGibbsSpike_rescaled_source_fisher_eq 0 m, egbFixedChargeAGibbsSpike_fisher_formula]

end
end GaloisForLFunctions.HTGeometry
