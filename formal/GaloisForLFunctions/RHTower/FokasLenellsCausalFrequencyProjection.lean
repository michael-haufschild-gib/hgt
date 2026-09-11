import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCore
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.FiniteDimension
/-! Canonical strong frequency projections on the genuine closed frequency span.
The actual contraction means converge for every vector in this complete carrier.
Their limits are norm-one rank-one projections with the exact frequency algebra. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencyProjectionLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencyProjectionChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencyProjectionChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencyProjectionChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace

private theorem dense_contraction_tendsto
    {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : I → E) (he : DenseRange e) (g : ℕ → E →L[ℂ] F) (p : E →L[ℂ] F)
    (hg : ∀ N x, ‖g N x‖ ≤ ‖x‖) (hp : ∀ x, ‖p x‖ ≤ ‖x‖)
    (ht : ∀ v, Tendsto (fun N => g N (e v)) atTop (𝓝 (p (e v)))) (u : E) :
    Tendsto (fun N => g N u) atTop (𝓝 (p u)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v, hv, huv⟩ : ∃ v : E, v ∈ Set.range e ∧ dist u v < ε/4 :=
    (Metric.mem_closure_iff (s := Set.range e) (a := u)).mp (he u) (ε/4) (by positivity)
  obtain ⟨q, hq⟩ := hv
  have htq : Tendsto (fun N => g N v) atTop (𝓝 (p v)) := hq ▸ ht q
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ N ≥ N₀, dist (g N v) (p v) < ε/2 :=
    Metric.tendsto_atTop.mp htq (ε/2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hleft : dist (g N u) (g N v) ≤ dist u v := by
    simpa only [dist_eq_norm, map_sub (g N)] using hg N (u-v)
  have hright : dist (p v) (p u) ≤ dist v u := by
    simpa only [dist_eq_norm, map_sub p] using hp (v-u)
  have hvu : dist v u < ε/4 := by simpa only [dist_comm] using huv
  have hmid := hN₀ N hN
  have htri := dist_triangle (g N u) (g N v) (p u)
  have htri' := dist_triangle (g N v) (p v) (p u)
  linarith

private theorem span_subtype_transfer
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (S : Submodule ℂ E) (x y : S)
    (h : x.val ∈ Submodule.span ℂ {y.val}) : x ∈ Submodule.span ℂ {y} := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc⟩

private theorem span_coefficient
    {E : Type*} [AddCommMonoid E] [Module ℂ E] (x y : E)
    (h : x ∈ Submodule.span ℂ {y}) : ∃ c : ℂ, c • y = x :=
  Submodule.mem_span_singleton.mp h

private theorem rankone_family_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : ℝ → E) (P : ℝ → E →L[ℂ] E)
    (hr : ∀ η u, P η u ∈ Submodule.span ℂ {v η})
    (hm : ∀ ω η, P ω (v η) = if ω = η then v η else 0) (ω η : ℝ) :
    (P ω).comp (P η) = if ω = η then P ω else 0 := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨c, hc⟩ := span_coefficient (P η u) (v η) (hr η u)
  have he : P ω (P η u) = c • P ω (v η) :=
    (congrArg (P ω) hc.symm).trans (map_smul (P ω) c (v η))
  by_cases h : ω = η
  · subst η
    rw [if_pos rfl]
    have ho : P ω (v ω) = v ω := by simpa only [if_pos rfl, ite_true] using hm ω ω
    exact he.trans ((congrArg (fun w : E => c • w) ho).trans hc)
  · rw [if_neg h]
    have hz : P ω (v η) = 0 := by simpa only [if_neg h] using hm ω η
    exact he.trans ((congrArg (fun w : E => c • w) hz).trans (smul_zero c))

/-- The actual closed complex-linear frequency span in the genuine derivative-chain norm. -/
def causalFrequencySpace (b : ℝ) : Submodule ℂ causalBoundedChain :=
  (causalFrequencyCore b).topologicalClosure

/-- The genuine closed frequency carrier is complete in the inherited chain norm. -/
theorem causalFrequencySpace_complete (b : ℝ) : CompleteSpace (causalFrequencySpace b) :=
  (causalFrequencyCore b).isClosed_topologicalClosure.completeSpace_coe

/-- An actual unit-frequency chain in the genuine closed frequency space. -/
def causalFrequencyMode (b η : ℝ) : causalFrequencySpace b :=
  ⟨causalBoundedUnitEigenchain b η,
    (causalFrequencyCore b).le_topologicalClosure (causalFrequencyCoreMode b η).property⟩

private def coreInclusion (b : ℝ) : causalFrequencyCore b →L[ℂ] causalFrequencySpace b :=
  (causalFrequencyCore b).subtypeL.codRestrict (causalFrequencySpace b)
    (fun u => (causalFrequencyCore b).le_topologicalClosure u.property)

private theorem coreInclusion_isometry (b : ℝ) : Isometry (coreInclusion b) := fun _ _ => rfl

private theorem coreInclusion_dense (b : ℝ) : DenseRange (coreInclusion b) :=
  (denseRange_inclusion_iff (causalFrequencyCore b).le_topologicalClosure).mpr (fun _ h => h)

private def extendedProjection (b ω : ℝ) : causalFrequencySpace b →L[ℂ] causalBoundedChain :=
  (causalFrequencyCoreProjection b ω).extend (coreInclusion b)

private theorem extended_on_core (b ω : ℝ) (u : causalFrequencyCore b) :
    extendedProjection b ω (coreInclusion b u) = causalFrequencyCoreProjection b ω u :=
  ContinuousLinearMap.extend_eq (causalFrequencyCoreProjection b ω) (coreInclusion_dense b)
    (coreInclusion_isometry b).isUniformInducing u

private theorem extended_norm_le (b ω : ℝ) : ‖extendedProjection b ω‖ ≤ 1 := by
  have h := ContinuousLinearMap.opNorm_extend_le (causalFrequencyCoreProjection b ω)
    (N := (1 : ℝ≥0)) (coreInclusion_dense b) (fun u => (one_mul ‖u‖).symm.le)
  simpa only [extendedProjection, norm_causalFrequencyCoreProjection, NNReal.coe_one, one_mul] using h

private theorem extended_mem_line (b ω : ℝ) (u : causalFrequencySpace b) :
    extendedProjection b ω u ∈ Submodule.span ℂ {causalBoundedUnitEigenchain b ω} := by
  refine (coreInclusion_dense b).induction_on
    (p := fun v : causalFrequencySpace b => extendedProjection b ω v ∈
      Submodule.span ℂ {causalBoundedUnitEigenchain b ω}) u ?_ ?_
  · exact (Submodule.span ℂ {causalBoundedUnitEigenchain b ω}).closed_of_finiteDimensional.preimage
      (extendedProjection b ω).continuous
  · intro v
    have hm : causalFrequencyCoreProjection b ω v ∈
        Submodule.span ℂ {causalBoundedUnitEigenchain b ω} := by
      exact (congrArg (fun S : Submodule ℂ causalBoundedChain =>
        causalFrequencyCoreProjection b ω v ∈ S) (causalFrequencyCoreProjection_range b ω)).mp
          (show causalFrequencyCoreProjection b ω v ∈
            LinearMap.range (causalFrequencyCoreProjection b ω).toLinearMap from ⟨v, rfl⟩)
    exact (congrArg (fun w : causalBoundedChain => w ∈
      Submodule.span ℂ {causalBoundedUnitEigenchain b ω}) (extended_on_core b ω v)).mpr hm

private theorem own_line_le_space (b ω : ℝ) :
    Submodule.span ℂ {causalBoundedUnitEigenchain b ω} ≤ causalFrequencySpace b := by
  apply Submodule.span_le.mpr
  intro v hv
  have he : v = causalBoundedUnitEigenchain b ω := Set.mem_singleton_iff.mp hv
  exact he.symm ▸ (causalFrequencyMode b ω).property

/-- The canonical completed frequency projection, extending the actual mean-limit
extractor and taking values in the genuine closed frequency carrier. -/
def causalFrequencyProjection (b ω : ℝ) : causalFrequencySpace b →L[ℂ] causalFrequencySpace b :=
  (extendedProjection b ω).codRestrict (causalFrequencySpace b)
    (fun u => own_line_le_space b ω (extended_mem_line b ω u))

private theorem projection_val (b ω : ℝ) (u : causalFrequencySpace b) :
    (causalFrequencyProjection b ω u).val = extendedProjection b ω u := rfl

private theorem extended_tendsto (b ω : ℝ) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N u.val)
      atTop (𝓝 (extendedProjection b ω u)) := by
  exact dense_contraction_tendsto (coreInclusion b) (coreInclusion_dense b)
    (fun N => (causalBoundedFrequencyMean b ω N).comp (causalFrequencySpace b).subtypeL)
    (extendedProjection b ω)
    (fun N v => by
      simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.coe_norm] using
        causalBoundedFrequencyMean_norm_apply_le b ω N v.val)
    (fun v => by
      simpa only [one_mul] using
        (extendedProjection b ω).le_of_opNorm_le (extended_norm_le b ω) v)
    (fun q => (congrArg (fun y : causalBoundedChain => Tendsto
      (fun N : ℕ => causalBoundedFrequencyMean b ω N q.val) atTop (𝓝 y))
        (extended_on_core b ω q)).mpr (causalFrequencyCoreProjection_tendsto b ω q)) u

/-- Actual frequency means converge strongly to the canonical projection on every
vector of the genuine closed frequency span. -/
theorem causalFrequencyProjection_tendsto (b ω : ℝ) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N u.val)
      atTop (𝓝 (causalFrequencyProjection b ω u).val) :=
  extended_tendsto b ω u

/-- The completed projection retains exactly its own genuine frequency mode. -/
theorem causalFrequencyProjection_mode (b ω η : ℝ) :
    causalFrequencyProjection b ω (causalFrequencyMode b η) =
      if ω = η then causalFrequencyMode b η else 0 := by
  have he : extendedProjection b ω (causalFrequencyMode b η) =
      if ω = η then causalBoundedUnitEigenchain b η else 0 :=
    (extended_on_core b ω (causalFrequencyCoreMode b η)).trans (causalFrequencyCoreProjection_mode b ω η)
  apply Subtype.ext
  by_cases h : ω = η
  · simpa only [if_pos h, projection_val, causalFrequencyMode] using he
  · simpa only [if_neg h, projection_val, Submodule.coe_zero] using he

private theorem projection_own (b ω : ℝ) :
    causalFrequencyProjection b ω (causalFrequencyMode b ω) = causalFrequencyMode b ω := by
  simpa only [if_pos rfl, ite_true] using causalFrequencyProjection_mode b ω ω

/-- The completed projection has exactly the actual one-dimensional frequency line as range. -/
theorem causalFrequencyProjection_range (b ω : ℝ) :
    LinearMap.range (causalFrequencyProjection b ω).toLinearMap =
      Submodule.span ℂ {causalFrequencyMode b ω} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u, hu⟩ : ∃ u : causalFrequencySpace b, causalFrequencyProjection b ω u = v := hv
    have hp : causalFrequencyProjection b ω u ∈ Submodule.span ℂ {causalFrequencyMode b ω} := by
      apply span_subtype_transfer (causalFrequencySpace b)
      exact (congrArg (fun v : causalBoundedChain => v ∈
        Submodule.span ℂ {causalBoundedUnitEigenchain b ω}) (projection_val b ω u)).mpr
          (extended_mem_line b ω u)
    exact hu ▸ hp
  · apply Submodule.span_le.mpr
    intro v hv
    have he : v = causalFrequencyMode b ω := Set.mem_singleton_iff.mp hv
    exact he.symm ▸ (show causalFrequencyMode b ω ∈
      LinearMap.range (causalFrequencyProjection b ω).toLinearMap from
      ⟨causalFrequencyMode b ω, projection_own b ω⟩)

/-- The exact frequency algebra: equal-frequency projections are idempotent,
while distinct-frequency projections annihilate one another. -/
theorem causalFrequencyProjection_comp (b ω η : ℝ) :
    (causalFrequencyProjection b ω).comp (causalFrequencyProjection b η) =
      if ω = η then causalFrequencyProjection b ω else 0 := by
  exact rankone_family_comp (causalFrequencyMode b) (causalFrequencyProjection b)
    (fun η u => (congrArg (fun S : Submodule ℂ (causalFrequencySpace b) =>
      causalFrequencyProjection b η u ∈ S) (causalFrequencyProjection_range b η)).mp
        (show causalFrequencyProjection b η u ∈
          LinearMap.range (causalFrequencyProjection b η).toLinearMap from ⟨u, rfl⟩))
    (causalFrequencyProjection_mode b) ω η

/-- Each canonical completed frequency projection has sharp norm one. -/
theorem norm_causalFrequencyProjection (b ω : ℝ) : ‖causalFrequencyProjection b ω‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    change ‖extendedProjection b ω u‖ ≤ 1 * ‖u‖
    exact (extendedProjection b ω).le_of_opNorm_le (extended_norm_le b ω) u
  · have hm : ‖causalFrequencyMode b ω‖ = 1 := norm_causalBoundedUnitEigenchain b ω
    have h := (causalFrequencyProjection b ω).le_opNorm (causalFrequencyMode b ω)
    simpa only [projection_own b ω, hm, mul_one] using h
end
end RHTower.FokasLenells
