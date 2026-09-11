import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCoefficient
import Mathlib.Order.Filter.Cofinite
/-! Frequency coefficients of every genuine closed-span vector vanish along the
cofinite filter. Positive threshold sets are finite, and the actual scalar support
is countable, even though the frequency label set is uncountable. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencySupportLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencySupportChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencySupportChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencySupportChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace

private theorem finite_support_on_span
    {I E : Type*} [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : I → E) (c : I → Submodule.span ℂ (Set.range v) →L[ℂ] ℂ)
    (hm : ∀ i j, c i ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ = if i = j then 1 else 0)
    (u : Submodule.span ℂ (Set.range v)) : (Function.support (fun i => c i u)).Finite := by
  classical
  refine Submodule.span_induction
    (p := fun x hx => (Function.support (fun i => c i ⟨x, hx⟩)).Finite) ?_ ?_ ?_ ?_ u.property
  · rintro _ ⟨j, rfl⟩
    apply (Set.finite_singleton j).subset
    intro i hi
    have hn : i = j := by
      by_contra h
      exact hi (by simpa only [if_neg h] using hm i j)
    exact Set.mem_singleton_iff.mpr hn
  · change (Function.support (fun i => c i 0)).Finite
    have hz : (fun i : I => c i 0) = (0 : I → ℂ) := funext (fun i => map_zero (c i))
    rw [hz, Function.support_zero]
    exact Set.finite_empty
  · intro x y hx hy hfx hfy
    apply (hfx.union hfy).subset
    intro i hi
    by_contra h
    have hx0 : c i ⟨x, hx⟩ = 0 := by
      by_contra hn
      exact h (Or.inl hn)
    have hy0 : c i ⟨y, hy⟩ = 0 := by
      by_contra hn
      exact h (Or.inr hn)
    apply hi
    change c i ((⟨x, hx⟩ : Submodule.span ℂ (Set.range v)) + ⟨y, hy⟩) = 0
    rw [map_add, hx0, hy0, add_zero]
  · intro a x hx hfx
    apply hfx.subset
    intro i hi
    by_cases hz : c i ⟨x, hx⟩ = 0
    · exfalso
      apply hi
      change c i (a • (⟨x, hx⟩ : Submodule.span ℂ (Set.range v))) = 0
      rw [map_smul, hz, smul_zero]
    · exact hz

private theorem cofinite_coefficients_of_dense
    {I J E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : J → E) (he : DenseRange e) (c : I → E →L[ℂ] ℂ)
    (hc : ∀ i x, ‖c i x‖ ≤ ‖x‖)
    (hf : ∀ q, (Function.support (fun i => c i (e q))).Finite) (u : E) :
    Tendsto (fun i => c i u) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv, huv⟩ : ∃ v : E, v ∈ Set.range e ∧ dist u v < ε :=
    (Metric.mem_closure_iff (s := Set.range e) (a := u)).mp (he u) ε hε
  obtain ⟨q, hq⟩ := hv
  have hfinite : (Function.support (fun i => c i v)).Finite := hq ▸ hf q
  have hz : ∀ᶠ i in cofinite, c i v = 0 := Filter.mem_cofinite.mpr hfinite
  filter_upwards [hz] with i hi
  calc
    dist (c i u) 0 = ‖c i (u-v)‖ := by rw [dist_zero_right, map_sub, hi, sub_zero]
    _ ≤ ‖u-v‖ := hc i (u-v)
    _ < ε := by simpa only [dist_eq_norm] using huv

private theorem coefficient_finite_threshold_iff
    {I : Type*} [Infinite I] (c : I → ℂ) (hc : Tendsto c cofinite (𝓝 0)) (ε : ℝ≥0) :
    {i | (ε : ℝ) ≤ ‖c i‖}.Finite ↔ ε ≠ 0 := by
  constructor
  · intro hf hzero
    have hu : (Set.univ : Set I).Finite := by
      simpa only [hzero, NNReal.coe_zero, norm_nonneg, Set.setOf_true] using hf
    exact Set.infinite_univ hu
  · intro hε
    have hpos : 0 < (ε : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hε)
    have h := Metric.tendsto_nhds.mp hc (ε : ℝ) hpos
    have hf := Filter.mem_cofinite.mp h
    simpa only [Set.compl_setOf, dist_zero_right, not_lt] using hf

private theorem coefficient_countable_support
    {I : Type*} (c : I → ℂ) (hc : Tendsto c cofinite (𝓝 0)) : (Function.support c).Countable := by
  simpa only [ker_nhds] using! hc.countable_compl_preimage_ker

private def coreLift (b : ℝ) : causalFrequencyCore b →L[ℂ] causalFrequencySpace b :=
  (causalFrequencyCore b).subtypeL.codRestrict (causalFrequencySpace b)
    (fun u => (causalFrequencyCore b).le_topologicalClosure u.property)

private theorem coreLift_dense (b : ℝ) : DenseRange (coreLift b) :=
  (denseRange_inclusion_iff (causalFrequencyCore b).le_topologicalClosure).mpr (fun _ h => h)

private theorem coreLift_mode (b η : ℝ) :
    coreLift b (causalFrequencyCoreMode b η) = causalFrequencyMode b η := rfl

private theorem core_finite_support (b : ℝ) (u : causalFrequencyCore b) :
    (Function.support (fun ω => causalFrequencyCoefficient b ω (coreLift b u))).Finite := by
  have h := finite_support_on_span (causalBoundedUnitEigenchain b)
    (fun ω => (causalFrequencyCoefficient b ω).comp (coreLift b))
    (fun ω η => by
      change causalFrequencyCoefficient b ω (coreLift b (causalFrequencyCoreMode b η)) = _
      exact (congrArg (causalFrequencyCoefficient b ω) (coreLift_mode b η)).trans
        (causalFrequencyCoefficient_mode b ω η)) u
  simpa only [ContinuousLinearMap.comp_apply] using! h

/-- Coefficients of every actual closed-span vector vanish outside finite sets at every scale. -/
theorem causalFrequencyCoefficient_tendsto_cofinite (b : ℝ) (u : causalFrequencySpace b) :
    Tendsto (fun ω : ℝ => causalFrequencyCoefficient b ω u) cofinite (𝓝 0) :=
  cofinite_coefficients_of_dense (coreLift b) (coreLift_dense b) (causalFrequencyCoefficient b)
    (fun ω v => by simpa only [one_mul] using
      (causalFrequencyCoefficient b ω).le_of_opNorm_le (norm_causalFrequencyCoefficient b ω).le v)
    (core_finite_support b) u

/-- A nonnegative amplitude threshold selects finitely many actual frequencies exactly when it is positive. -/
theorem causalFrequencyCoefficient_finite_threshold_iff (b : ℝ) (u : causalFrequencySpace b) (ε : ℝ≥0) :
    {ω : ℝ | (ε : ℝ) ≤ ‖causalFrequencyCoefficient b ω u‖}.Finite ↔ ε ≠ 0 :=
  coefficient_finite_threshold_iff (fun ω => causalFrequencyCoefficient b ω u)
    (causalFrequencyCoefficient_tendsto_cofinite b u) ε

/-- Every vector of the actual complete frequency space has at most countably many nonzero coefficients. -/
theorem causalFrequencyCoefficient_countable_support (b : ℝ) (u : causalFrequencySpace b) :
    (Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u)).Countable :=
  coefficient_countable_support (fun ω => causalFrequencyCoefficient b ω u)
    (causalFrequencyCoefficient_tendsto_cofinite b u)
end
end RHTower.FokasLenells
