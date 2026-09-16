import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspIndicialSelection
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSmoothOnsetLaplace

/-!
# Literal on-shell source pole for the Peierls continuation

The causal source transform is a pole plus the entire correction from its fixed smooth onset.
At the constructed Einstein frequency `w = 2 * physicalRate`, its normalized residue is one,
so that uncorrected transform cannot be continued holomorphically through the on-shell point.
The residue is the compulsory surviving boundary cochain for any literal meromorphic realization.
-/

namespace RHTower.D4BMLiteralOnShellSourcePole

open D4BMCuspProjection D4BMModularCore
open Filter Topology

noncomputable section

/-- The fixed smooth-onset continuation has unit normalized residue at its displayed source pole. -/
theorem smoothOnset_pole_residue (v : ℂ) :
    Tendsto (fun w : ℂ => (w - v) * (1 / (w - v) + onsetCorrection v w))
      (𝓝[≠] v) (𝓝 1) := by
  let g : ℂ → ℂ := fun w => 1 + (w - v) * onsetCorrection v w
  have hg : Differentiable ℂ g := by
    dsimp only [g]
    exact (differentiable_const (1 : ℂ)).add
      ((differentiable_id.sub (differentiable_const v)).mul (onsetCorrection_entire v))
  have hvalue : g v = 1 := by
    simp [g]
  have hT : Tendsto g (𝓝[≠] v) (𝓝 1) := by
    have hT0 : Tendsto g (𝓝[≠] v) (𝓝 (g v)) :=
      hg.continuous.continuousAt.continuousWithinAt.tendsto
    rw [hvalue] at hT0
    exact hT0
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hsub : w - v ≠ 0 := sub_ne_zero.mpr hw
  change g w = (w - v) * (1 / (w - v) + onsetCorrection v w)
  field_simp [hsub]
  simp only [g]

/-- No holomorphic causal source transform can retain the uncorrected onset through its source pole. -/
theorem smoothOnset_not_continuous (v : ℂ) :
    ¬ ContinuousAt (fun w : ℂ => 1 / (w - v) + onsetCorrection v w) v := by
  intro hc
  have hres := smoothOnset_pole_residue v
  have hlin : Tendsto (fun w : ℂ => w - v) (𝓝[≠] v) (𝓝 (0 : ℂ)) := by
    have hlin0 : ContinuousAt (fun w : ℂ => w - v) v :=
      continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℂ => v) v)
    simpa using hlin0.continuousWithinAt.tendsto
  have hcont : Tendsto (fun w : ℂ => 1 / (w - v) + onsetCorrection v w)
      (𝓝[≠] v) (𝓝 (1 / (v - v) + onsetCorrection v v)) :=
    hc.continuousWithinAt.tendsto
  have hzero : Tendsto (fun w : ℂ =>
      (w - v) * (1 / (w - v) + onsetCorrection v w)) (𝓝[≠] v) (𝓝 (0 : ℂ)) := by
    simpa using hlin.mul hcont
  have hEq : (0 : ℂ) = 1 := tendsto_nhds_unique hzero hres
  norm_num at hEq

/-- The preceding non-continuity excludes analytic continuation of the uncorrected source. -/
theorem smoothOnset_not_analyticAt (v : ℂ) :
    ¬ AnalyticAt ℂ (fun w : ℂ => 1 / (w - v) + onsetCorrection v w) v := by
  intro h
  exact smoothOnset_not_continuous v h.continuousAt

/-- At each physical Einstein frequency, the literal onset transform has the unit source residue. -/
theorem physicalOnShell_sourcePole_residue (q : XiZeroCopy) (branch : Bool) :
    Tendsto (fun w : ℂ =>
      (w - 2 * physicalRate q branch) *
        (1 / (w - 2 * physicalRate q branch) +
          onsetCorrection (2 * physicalRate q branch) w))
      (𝓝[≠] (2 * physicalRate q branch)) (𝓝 1) := by
  exact smoothOnset_pole_residue (2 * physicalRate q branch)

/-- Thus the literal on-shell source admits no uncorrected holomorphic continuation. -/
theorem physicalOnShell_sourcePole_not_analyticAt (q : XiZeroCopy) (branch : Bool) :
    ¬ AnalyticAt ℂ (fun w : ℂ =>
      1 / (w - 2 * physicalRate q branch) +
        onsetCorrection (2 * physicalRate q branch) w)
      (2 * physicalRate q branch) := by
  exact smoothOnset_not_analyticAt (2 * physicalRate q branch)

end
end RHTower.D4BMLiteralOnShellSourcePole
