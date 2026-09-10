import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedFrequencyMeans
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Bases

/-! Topology of the genuine bounded Cauchy derivative chain space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalChainTopologyLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalChainTopologyChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalChainTopologyChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalChainTopologyChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
/-- The genuine supremum-over-derivatives norm admits no countable dense set of chains. -/
theorem causalBoundedChain_not_separable : ¬TopologicalSpace.SeparableSpace causalBoundedChain := by
  intro h
  letI : TopologicalSpace.SeparableSpace causalBoundedChain := h
  have hballs : Pairwise (Function.onFun Disjoint
      (fun ω : ℝ => Metric.ball (causalBoundedUnitEigenchain 0 ω) (1 / 2 : ℝ))) := by
    intro ω η hne
    apply Metric.ball_disjoint_ball
    have hs := causalBoundedUnitEigenchain_pairwise_separated 0 hne
    norm_num only at ⊢
    exact hs
  have hc : Countable ℝ := hballs.countable_of_isOpen_disjoint
    (fun _ => Metric.isOpen_ball)
    (fun ω => ⟨causalBoundedUnitEigenchain 0 ω, Metric.mem_ball_self (by norm_num)⟩)
  exact not_countable hc

/-- Every frequency is a discontinuity of the actual unit-chain family in its bounded norm. -/
theorem causalBoundedUnitEigenchain_not_continuousAt (b ω : ℝ) :
    ¬ContinuousAt (causalBoundedUnitEigenchain b) ω := by
  intro hc
  have ht : Tendsto (fun n : ℕ => ω + 1 / ((n : ℝ) + 1)) atTop (𝓝 ω) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := ω)).add tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun n : ℕ => dist
      (causalBoundedUnitEigenchain b (ω + 1 / ((n : ℝ) + 1)))
      (causalBoundedUnitEigenchain b ω)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, dist_self] using (hc.tendsto.comp ht).dist
      (tendsto_const_nhds (x := causalBoundedUnitEigenchain b ω))
  have hsep (n : ℕ) : 1 ≤ dist
      (causalBoundedUnitEigenchain b (ω + 1 / ((n : ℝ) + 1)))
      (causalBoundedUnitEigenchain b ω) := by
    apply causalBoundedUnitEigenchain_pairwise_separated b
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hh : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hd hsep
  norm_num at hh

end
end RHTower.FokasLenells
