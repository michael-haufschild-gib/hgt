import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeBoundaryIntegrals
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! # Exact setwise error and genuine weak convergence of the finite source -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter
attribute [local instance] Classical.propDecidable

private theorem atom_real (w : NNReal) (y : HausdorffSourceSpace) (S : Set HausdorffSourceSpace) :
    (hausdorffAtomSource w y).real S = (w : ℝ) * (if y ∈ S then 1 else 0) := by
  classical
  rw [hausdorffAtomSource, measureReal_nnreal_smul_apply]
  by_cases h : y ∈ S <;> simp [Measure.real, Measure.dirac_apply, h]

/-- Setwise error depends on three membership indicators, even for arbitrary sets. -/
theorem egbFixedChargeAGibbsSpike_set_error (n : ℕ) (S : Set HausdorffSourceSpace) :
    (egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)).real S -
      egbFixedChargeAGibbsSpikeBoundarySource.real S =
      (-5 * (if egbFixedChargeAGibbsCollisionZeroNode ∈ S then 1 else 0) +
        2 * (if egbFixedChargeAGibbsCollisionSlowNode ∈ S then 1 else 0) +
        2 * (if egbFixedChargeAGibbsCollisionFastNode ∈ S then 1 else 0)) /
          (4 * (2 : ℝ) ^ (n + 3)) := by
  classical
  rw [egbFixedChargeAGibbsFullCollisionHausdorffSource, measureReal_add_apply,
    measureReal_add_apply, egbFixedChargeAGibbsSpikeBoundarySource]
  rw [atom_real, atom_real, atom_real, atom_real]
  change egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) * _ +
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) * _ +
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) * _ - (1 / 4 : ℝ) * _ = _
  rw [egbFixedChargeAGibbsSpike_discarded_energy, egbFixedChargeAGibbsSpike_slow_energy,
    egbFixedChargeAGibbsSpike_fast_energy]
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hn]
  <;> ring

/-- The sharp setwise bound is five over four grid sizes, distinct from total variation mass. -/
theorem egbFixedChargeAGibbsSpike_set_error_bound (n : ℕ) (S : Set HausdorffSourceSpace) :
    |(egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)).real S -
      egbFixedChargeAGibbsSpikeBoundarySource.real S| ≤ 5 / (4 * (2 : ℝ) ^ (n + 3)) := by
  classical
  have hi (y : HausdorffSourceSpace) : (0 : ℝ) ≤ (if y ∈ S then 1 else 0) ∧
      (if y ∈ S then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hnum : |-5 * (if egbFixedChargeAGibbsCollisionZeroNode ∈ S then (1 : ℝ) else 0) +
      2 * (if egbFixedChargeAGibbsCollisionSlowNode ∈ S then 1 else 0) +
      2 * (if egbFixedChargeAGibbsCollisionFastNode ∈ S then 1 else 0)| ≤ 5 := by
    have h0 := hi egbFixedChargeAGibbsCollisionZeroNode
    have hr := hi egbFixedChargeAGibbsCollisionSlowNode
    have hs := hi egbFixedChargeAGibbsCollisionFastNode
    rw [abs_le]
    constructor <;> linarith
  have hd : 0 < 4 * (2 : ℝ) ^ (n + 3) := by positivity
  rw [egbFixedChargeAGibbsSpike_set_error, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hnum hd.le

/-- The measurable singleton endpoint attains the negative setwise error. -/
theorem egbFixedChargeAGibbsSpike_endpoint_set_error (n : ℕ) :
    (egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)).real
        {egbFixedChargeAGibbsCollisionZeroNode} -
      egbFixedChargeAGibbsSpikeBoundarySource.real {egbFixedChargeAGibbsCollisionZeroNode} =
      -(5 / (4 * (2 : ℝ) ^ (n + 3))) := by
  rw [egbFixedChargeAGibbsSpike_set_error]
  have hr : egbFixedChargeAGibbsCollisionSlowNode ≠ egbFixedChargeAGibbsCollisionZeroNode := by
    intro h
    have hv := congrArg (fun y : HausdorffSourceSpace => (y : ℝ)) h
    norm_num [egbFixedChargeAGibbsCollisionSlowNode, egbFixedChargeAGibbsCollisionZeroNode] at hv
  have hs : egbFixedChargeAGibbsCollisionFastNode ≠ egbFixedChargeAGibbsCollisionZeroNode := by
    intro h
    have hv := congrArg (fun y : HausdorffSourceSpace => (y : ℝ)) h
    norm_num [egbFixedChargeAGibbsCollisionFastNode, egbFixedChargeAGibbsCollisionZeroNode] at hv
  simp only [Set.mem_singleton_iff, hr, hs, if_false, if_true, mul_one, mul_zero, add_zero]
  ring

/-- The exact maximum discrepancy over measurable sets. -/
theorem egbFixedChargeAGibbsSpike_setwise_maximum (n : ℕ) :
    IsGreatest {z : ℝ | ∃ S : Set HausdorffSourceSpace, MeasurableSet S ∧
      z = |(egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)).real S -
        egbFixedChargeAGibbsSpikeBoundarySource.real S|}
      (5 / (4 * (2 : ℝ) ^ (n + 3))) := by
  constructor
  · refine ⟨{egbFixedChargeAGibbsCollisionZeroNode}, measurableSet_singleton _, ?_⟩
    rw [egbFixedChargeAGibbsSpike_endpoint_set_error, abs_neg, abs_of_nonneg (by positivity)]
  · rintro z ⟨S, _, rfl⟩
    exact egbFixedChargeAGibbsSpike_set_error_bound n S

def egbFixedChargeAGibbsSpikeFiniteSource (n : ℕ) : MeasureTheory.FiniteMeasure HausdorffSourceSpace :=
  ⟨egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n), inferInstance⟩

def egbFixedChargeAGibbsSpikeFiniteBoundary : MeasureTheory.FiniteMeasure HausdorffSourceSpace :=
  ⟨egbFixedChargeAGibbsSpikeBoundarySource, inferInstance⟩

/-- The actual sequence converges in mathlib's weak topology of finite measures. -/
theorem egbFixedChargeAGibbsSpike_source_weak_tendsto_boundary :
    Tendsto egbFixedChargeAGibbsSpikeFiniteSource atTop (nhds egbFixedChargeAGibbsSpikeFiniteBoundary) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact egbFixedChargeAGibbsSpike_integrals_tendsto_boundary f

end
end GaloisForLFunctions.HTGeometry
