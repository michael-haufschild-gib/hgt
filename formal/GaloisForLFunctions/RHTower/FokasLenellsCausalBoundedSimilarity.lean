import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedInverseCondition
import GaloisForLFunctions.HilbertMetric.PseudospectrumSimilarity

/-! Apply the corpus's resolvent and pseudospectrum similarity theorem to the actual causal
entire bounded-chain group, with its exact complex-time amplification factor. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing


open GaloisForLFunctions.HilbertMetric
local instance : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance : Nontrivial (causalBoundedChain →L[ℂ] causalBoundedChain) := by
  refine ⟨⟨causalBoundedChainExponential 0, 0, ?_⟩⟩
  intro h
  have hn : ‖causalBoundedChainExponential 0‖ = 0 :=
    (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖) h).trans (norm_zero)
  have hge := one_le_norm_causalBoundedChainExponential 0
  linarith only [hn, hge]

/-- The actual entire forward and reverse evolutions form a unit of the operator ring. -/
def causalBoundedEntireUnit (z : ℂ) : (causalBoundedChain →L[ℂ] causalBoundedChain)ˣ where
  val := causalBoundedChainExponential z
  inv := causalBoundedChainExponential (-z)
  val_inv := by
    apply ContinuousLinearMap.ext
    intro u
    exact causalBoundedChainExponential_apply_neg z u
  inv_val := by
    apply ContinuousLinearMap.ext
    intro u
    exact causalBoundedChainExponential_neg_apply z u

/-- The existing corpus condition number is exactly the proved genuine complex-time cost. -/
theorem causalBoundedEntireUnit_condition (z : ℂ) :
    similarityConditionNumber (causalBoundedEntireUnit z) = Real.exp (‖z‖ + |z.im|) :=
  causalBoundedEntireCondition_eq z

/-- Recode an actual bounded operator by the genuine entire causal evolution. -/
def causalBoundedSimilarity (z : ℂ) (A : causalBoundedChain →L[ℂ] causalBoundedChain) :
    causalBoundedChain →L[ℂ] causalBoundedChain :=
  causalBoundedChainExponential z * A * causalBoundedChainExponential (-z)

/-- Genuine complex-time recoding preserves the exact spectrum of every bounded operator. -/
theorem causalBoundedSimilarity_spectrum (z : ℂ)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain) :
    spectrum ℂ (causalBoundedSimilarity z A) = spectrum ℂ A := by
  exact spectrum.units_conjugate (u := causalBoundedEntireUnit z)

/-- The actual resolvent is transported literally through the causal similarity. -/
theorem causalBoundedSimilarity_resolvent (z w : ℂ)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain) :
    resolvent (causalBoundedSimilarity z A) w =
      causalBoundedChainExponential z * resolvent A w * causalBoundedChainExponential (-z) :=
  resolvent_units_conjugate (causalBoundedEntireUnit z) A w

/-- The actual time-dependent condition factor controls the recoded resolvent. -/
theorem causalBoundedSimilarity_resolvent_norm_le (z w : ℂ)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain) :
    ‖resolvent (causalBoundedSimilarity z A) w‖ ≤
      Real.exp (‖z‖ + |z.im|) * ‖resolvent A w‖ := by
  have h := norm_resolvent_units_conjugate_le (causalBoundedEntireUnit z) A w
  have he := congrArg (fun c : ℝ => c*‖resolvent A w‖) (causalBoundedEntireUnit_condition z)
  exact h.trans_eq he

/-- The same exact factor controls reconstruction of the original resolvent. -/
theorem causalBoundedSimilarity_resolvent_reverse_norm_le (z w : ℂ)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain) :
    ‖resolvent A w‖ ≤ Real.exp (‖z‖ + |z.im|) * ‖resolvent (causalBoundedSimilarity z A) w‖ := by
  have h := norm_resolvent_le_conditionNumber_mul_conjugate (causalBoundedEntireUnit z) A w
  have he := congrArg (fun c : ℝ => c*‖resolvent (causalBoundedSimilarity z A) w‖)
    (causalBoundedEntireUnit_condition z)
  exact h.trans_eq he

/-- The explicit smaller pseudospectral tolerance is positive for every actual complex time. -/
def causalBoundedSimilaritySmallScale (z : ℂ) (ε : PseudospectralScale) : PseudospectralScale :=
  ⟨ε.val / Real.exp (‖z‖ + |z.im|), div_pos ε.property (Real.exp_pos _)⟩

/-- The explicit larger tolerance uses the same exact actual condition factor. -/
def causalBoundedSimilarityLargeScale (z : ℂ) (ε : PseudospectralScale) : PseudospectralScale :=
  ⟨ε.val * Real.exp (‖z‖ + |z.im|), mul_pos ε.property (Real.exp_pos _)⟩

/-- The corpus pseudospectral sandwich applies with explicit, unconditional complex-time scales. -/
theorem causalBoundedSimilarity_pseudospectrum_sandwich (z : ℂ) (ε : PseudospectralScale)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain) :
    normResolventPseudospectrum ℂ (causalBoundedSimilaritySmallScale z ε) A ⊆
        normResolventPseudospectrum ℂ ε (causalBoundedSimilarity z A) ∧
      normResolventPseudospectrum ℂ ε (causalBoundedSimilarity z A) ⊆
        normResolventPseudospectrum ℂ (causalBoundedSimilarityLargeScale z ε) A := by
  have hs : ε.divConditionNumber (causalBoundedEntireUnit z) = causalBoundedSimilaritySmallScale z ε := by
    apply Subtype.ext
    exact congrArg (fun c : ℝ => ε.val/c) (causalBoundedEntireUnit_condition z)
  have hl : ε.mulConditionNumber (causalBoundedEntireUnit z) = causalBoundedSimilarityLargeScale z ε := by
    apply Subtype.ext
    exact congrArg (fun c : ℝ => ε.val*c) (causalBoundedEntireUnit_condition z)
  have h := normResolventPseudospectrum_similarity_sandwich (𝕜 := ℂ) ε (causalBoundedEntireUnit z) A
  simpa only [hs, hl] using! h

end
end RHTower.FokasLenells
