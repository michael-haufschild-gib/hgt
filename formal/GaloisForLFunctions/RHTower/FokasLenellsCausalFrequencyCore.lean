import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedFrequencyMeans
import Mathlib.Analysis.Normed.Operator.Completeness
/-! Canonical norm-one frequency extraction on finite sums of genuine bounded
Cauchy derivative eigenchains. The projection is the actual pointwise mean limit,
with no assumed coefficient representation or independence of the input modes. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencyCoreLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencyCoreChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencyCoreChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencyCoreChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace

/-- The genuine finite complex-linear span of the actual unit-frequency derivative chains. -/
def causalFrequencyCore (b : ℝ) : Submodule ℂ causalBoundedChain :=
  Submodule.span ℂ (Set.range (causalBoundedUnitEigenchain b))

/-- An actual unit-frequency chain regarded as a member of its genuine finite core. -/
def causalFrequencyCoreMode (b η : ℝ) : causalFrequencyCore b :=
  ⟨causalBoundedUnitEigenchain b η, Submodule.subset_span (Set.mem_range_self η)⟩

private theorem core_limit_exists (b ω : ℝ) (u : causalFrequencyCore b) :
    ∃ c : ℂ, Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N u.val)
      atTop (𝓝 (c • causalBoundedUnitEigenchain b ω)) := by
  refine Submodule.span_induction
    (p := fun v _ => ∃ c : ℂ, Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N v)
      atTop (𝓝 (c • causalBoundedUnitEigenchain b ω))) ?_ ?_ ?_ ?_ u.property
  · rintro _ ⟨η, rfl⟩
    by_cases h : ω = η
    · subst η
      refine ⟨1, ?_⟩
      simpa only [ite_true, one_smul] using causalBoundedFrequencyMean_tendsto_unitEigenchain b ω ω
    · refine ⟨0, ?_⟩
      simpa only [if_neg h, zero_smul] using causalBoundedFrequencyMean_tendsto_unitEigenchain b ω η
  · refine ⟨0, ?_⟩
    simpa only [map_zero, zero_smul] using (tendsto_const_nhds (x := (0 : causalBoundedChain)))
  · rintro x y _ _ ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c+d, ?_⟩
    simpa only [map_add, add_smul] using hc.add hd
  · rintro a x _ ⟨c, hc⟩
    refine ⟨a*c, ?_⟩
    simpa only [map_smul, smul_smul] using hc.const_smul a

private def coreScalar (b ω : ℝ) (u : causalFrequencyCore b) : ℂ :=
  Classical.choose (core_limit_exists b ω u)

private def coreLimit (b ω : ℝ) (u : causalFrequencyCore b) : causalBoundedChain :=
  coreScalar b ω u • causalBoundedUnitEigenchain b ω

private theorem coreLimit_tendsto (b ω : ℝ) (u : causalFrequencyCore b) :
    Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N u.val) atTop (𝓝 (coreLimit b ω u)) :=
  Classical.choose_spec (core_limit_exists b ω u)

private theorem core_mean_norm_le (b ω : ℝ) (N : ℕ) :
    ‖(causalBoundedFrequencyMean b ω N).comp (causalFrequencyCore b).subtypeL‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖causalBoundedFrequencyMean b ω N u.val‖ ≤ 1 * ‖u‖
  simpa only [one_mul, Submodule.coe_norm] using causalBoundedFrequencyMean_norm_apply_le b ω N u.val

/-- The canonical frequency extractor on the genuine finite core, obtained from
the actual mean limit and its uniform operator bound. -/
def causalFrequencyCoreProjection (b ω : ℝ) : causalFrequencyCore b →L[ℂ] causalBoundedChain :=
  ContinuousLinearMap.ofTendstoOfBoundedRange (coreLimit b ω)
    (fun N : ℕ => (causalBoundedFrequencyMean b ω N).comp (causalFrequencyCore b).subtypeL)
    (tendsto_pi_nhds.mpr (fun u => coreLimit_tendsto b ω u))
    (isBounded_iff_forall_norm_le.mpr ⟨1, by
      rintro _ ⟨N, rfl⟩
      exact core_mean_norm_le b ω N⟩)

/-- Every actual finite superposition has a genuine mean limit equal to its
canonical extracted frequency component. -/
theorem causalFrequencyCoreProjection_tendsto (b ω : ℝ) (u : causalFrequencyCore b) :
    Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N u.val)
      atTop (𝓝 (causalFrequencyCoreProjection b ω u)) :=
  coreLimit_tendsto b ω u

/-- The canonical core projection fixes its own actual mode and kills every other mode. -/
theorem causalFrequencyCoreProjection_mode (b ω η : ℝ) :
    causalFrequencyCoreProjection b ω (causalFrequencyCoreMode b η) =
      if ω = η then causalBoundedUnitEigenchain b η else 0 :=
  tendsto_nhds_unique (causalFrequencyCoreProjection_tendsto b ω (causalFrequencyCoreMode b η))
    (causalBoundedFrequencyMean_tendsto_unitEigenchain b ω η)

private theorem projection_own (b ω : ℝ) :
    causalFrequencyCoreProjection b ω (causalFrequencyCoreMode b ω) = causalBoundedUnitEigenchain b ω := by
  simpa only [if_pos rfl, ite_true] using causalFrequencyCoreProjection_mode b ω ω

/-- The extractor's range is exactly the one-dimensional actual frequency line. -/
theorem causalFrequencyCoreProjection_range (b ω : ℝ) :
    LinearMap.range (causalFrequencyCoreProjection b ω).toLinearMap =
      Submodule.span ℂ {causalBoundedUnitEigenchain b ω} := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨coreScalar b ω u, rfl⟩
  · apply Submodule.span_le.mpr
    intro v hv
    have he : v = causalBoundedUnitEigenchain b ω := Set.mem_singleton_iff.mp hv
    exact he.symm ▸ (show causalBoundedUnitEigenchain b ω ∈
      LinearMap.range (causalFrequencyCoreProjection b ω).toLinearMap from
      ⟨causalFrequencyCoreMode b ω, projection_own b ω⟩)

/-- Frequency extraction has sharp norm one on the actual finite core. -/
theorem norm_causalFrequencyCoreProjection (b ω : ℝ) : ‖causalFrequencyCoreProjection b ω‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    have h := le_of_tendsto (causalFrequencyCoreProjection_tendsto b ω u).norm
      (Filter.Eventually.of_forall (fun N => causalBoundedFrequencyMean_norm_apply_le b ω N u.val))
    simpa only [one_mul, Submodule.coe_norm] using h
  · have hm : ‖causalFrequencyCoreMode b ω‖ = 1 := norm_causalBoundedUnitEigenchain b ω
    have h := (causalFrequencyCoreProjection b ω).le_opNorm (causalFrequencyCoreMode b ω)
    simpa only [projection_own b ω, hm, norm_causalBoundedUnitEigenchain, mul_one] using h
end
end RHTower.FokasLenells
