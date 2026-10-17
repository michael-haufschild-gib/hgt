import GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift
import GaloisForLFunctions.HTGeometry.StrongConvergenceDense

/-!
# Strong continuity of the Burnol weighted shifts

The dense depth eigenfeatures and the uniform contraction bound give norm
continuity of every weighted-shift trajectory, including at time zero.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

theorem continuous_burnolWeightedShift_apply (f : BurnolHalfLineL2) :
    Continuous (fun h : ℝ≥0 => burnolWeightedShift h f) := by
  apply continuous_iff_continuousAt.mpr
  intro h₀
  apply tendsto_of_dense_of_uniform_bound (C := 1) zero_le_one
    (Eventually.of_forall norm_burnolWeightedShift_le)
    (norm_burnolWeightedShift_le h₀) (dense_burnolDepthSpan ⟨1, by norm_num⟩)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨n, rfl⟩ := hv
    have hc : Continuous (fun h : ℝ≥0 =>
        ((Real.exp (-(h * ((n + 1 : ℝ) * (1 : ℝ)))) : ℝ) : ℂ)) := by fun_prop
    simpa only [burnolWeightedShift_depthFeature] using
      (hc.tendsto h₀).smul (tendsto_const_nhds (x := burnolDepthFeatureL2 ⟨1, by norm_num⟩ n))
  | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : BurnolHalfLineL2)))
  | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
  | smul c x hx ih => simpa only [map_smul] using (tendsto_const_nhds (x := c)).smul ih

theorem tendsto_burnolWeightedShift_zero (f : BurnolHalfLineL2) :
    Tendsto (fun h : ℝ≥0 => burnolWeightedShift h f) (𝓝 0) (𝓝 f) := by
  have hzero : burnolWeightedShift 0 f = f := by
    apply Lp.ext
    filter_upwards [burnolWeightedShift_coeFn 0 f, ae_restrict_mem measurableSet_Ioi]
      with t ht hpos
    have htpos : (0 : ℝ) < t := hpos
    simpa [htpos.ne'] using ht
  simpa only [hzero] using (continuous_burnolWeightedShift_apply f).tendsto 0

end GaloisForLFunctions.HTGeometry
