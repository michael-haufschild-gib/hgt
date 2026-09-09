import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorGraph
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exact analytic-core action of the maximal causal generator

The common raw core is sent to its literal lower Hardy Cauchy data. Its
complex analytic hierarchy supplies actual right derivatives for the completed
semigroup. Consequently the maximal generator contains this dense encoded
subspace and acts there by the first compressed raw multiplier. The sharp
raw-order obstruction proves the actual generator unbounded in the data norm.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual signed Cauchy map with its exact lower Hardy codomain. -/
def lowerHardyCauchyMap : SoninL2 →L[ℂ] hardyL2ᗮ :=
  negativeCauchy.codRestrict (hardyL2ᗮ)
    (fun u => (negativeCauchy_eq_neg_iff _).1 (negativeCauchy_square u))

/-- The actual Cauchy encoding of the common analytic core into completed data. -/
def causalAnalyticCoreEmbedding : rawComplexEntireCore →L[ℂ] hardyL2ᗮ :=
  lowerHardyCauchyMap.comp rawComplexEntireCore.subtypeL

/-- The lower Hardy hierarchy retains the literal Cauchy-compressed raw values. -/
def causalAnalyticCoreHierarchy (n : ℕ) (τ : ℂ) : rawComplexEntireCore →ₗ[ℂ] hardyL2ᗮ :=
  causalAnalyticCoreEmbedding.toLinearMap.comp (rawComplexCoreHierarchy n τ)

/-- Completed core encoding is exactly the earlier isometric inclusion of encoded data. -/
theorem causalAnalyticCoreEmbedding_eq (u : rawComplexEntireCore) :
    causalAnalyticCoreEmbedding u = cauchyCoreLowerEmbedding (rawComplexCauchyCoreEncoding u) := by
  apply Subtype.ext
  rfl

/-- Actual encoded analytic data are dense in the completed lower Hardy space. -/
theorem causalAnalyticCoreEmbedding_denseRange : DenseRange causalAnalyticCoreEmbedding := by
  have he : Set.range causalAnalyticCoreEmbedding = Set.range cauchyCoreLowerEmbedding := by
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨rawComplexCauchyCoreEncoding u,(causalAnalyticCoreEmbedding_eq u).symm⟩
    · rintro ⟨u,rfl⟩
      obtain ⟨v,rfl⟩ := rawComplexCauchyCoreEncoding.surjective u
      exact ⟨v,causalAnalyticCoreEmbedding_eq v⟩
  intro y
  rw [he]
  exact cauchyCoreLowerEmbedding_denseRange y

/-- Every order has its genuine complex derivative in the lower Hardy norm. -/
theorem causalAnalyticCoreHierarchy_hasDerivAt (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    HasDerivAt (fun σ => causalAnalyticCoreHierarchy n σ u)
      (causalAnalyticCoreHierarchy (n+1) τ u) τ :=
  lowerHardyCauchyMap.hasFDerivAt.comp_hasDerivAt τ (rawComplexCoreHierarchy_hasDerivAt n τ u)

/-- Restricting the actual entire hierarchy to real times keeps the same vector derivative. -/
theorem causalAnalyticCoreHierarchy_hasRealDerivAt (n : ℕ) (t : ℝ) (u : rawComplexEntireCore) :
    HasDerivAt (fun s : ℝ => causalAnalyticCoreHierarchy n (s:ℂ) u)
      (causalAnalyticCoreHierarchy (n+1) (t:ℂ) u) t := by
  have hd := causalAnalyticCoreHierarchy_hasDerivAt n (t:ℂ) u
  simpa using! ((hd.hasFDerivAt.restrictScalars ℝ).comp t Complex.ofRealCLM.hasFDerivAt).hasDerivAt

/-- The completed causal orbit is the literal entire core orbit at nonnegative real time. -/
theorem causalAnalyticCoreEmbedding_evolution (t : ℝ≥0) (u : rawComplexEntireCore) :
    causalLowerCauchyEvolution t (causalAnalyticCoreEmbedding u) =
      causalAnalyticCoreHierarchy 0 ((t:ℝ):ℂ) u := by
  apply Subtype.ext
  change -negativeCauchy (evolution t (negativeCauchy u.val)) =
    negativeCauchy (rawComplexCoreHierarchy 0 ((t:ℝ):ℂ) u).val
  rw [rawComplexCoreHierarchy_zero_ofReal,negativeCauchy_causal_sandwich,neg_neg]

/-- Every encoded analytic vector has its exact first-order actual right derivative. -/
theorem causalAnalyticCoreEmbedding_hasRightDeriv (u : rawComplexEntireCore) :
    HasDerivWithinAt (causalForwardOrbit (causalAnalyticCoreEmbedding u))
      (causalAnalyticCoreHierarchy 1 0 u) (Ioi 0) 0 := by
  have hd := causalAnalyticCoreHierarchy_hasRealDerivAt 0 0 u
  simp only [zero_add,Complex.ofReal_zero] at hd
  apply hd.hasDerivWithinAt.congr
  · intro r hr
    change causalLowerCauchyEvolution r.toNNReal (causalAnalyticCoreEmbedding u) = _
    rw [causalAnalyticCoreEmbedding_evolution,Real.coe_toNNReal r hr.le]
  · rw [causalForwardOrbit_zero]
    change causalAnalyticCoreEmbedding u = causalAnalyticCoreEmbedding (rawComplexCoreHierarchy 0 (0:ℂ) u)
    rw [rawComplexCoreHierarchy_initial]

/-- Every actual encoded analytic vector belongs to the maximal derivative domain. -/
theorem causalAnalyticCoreEmbedding_mem_domain (u : rawComplexEntireCore) :
    causalAnalyticCoreEmbedding u ∈ causalGeneratorDomain :=
  (causalGeneratorDomain_mem_iff _).2 ⟨_,causalAnalyticCoreEmbedding_hasRightDeriv u⟩

/-- The actual encoded analytic data as elements of the proved maximal domain. -/
def causalAnalyticCoreDomainMap : rawComplexEntireCore →ₗ[ℂ] causalGeneratorDomain :=
  causalAnalyticCoreEmbedding.toLinearMap.codRestrict causalGeneratorDomain
    causalAnalyticCoreEmbedding_mem_domain

/-- The maximal generator acts on encoded analytic data by exactly the first compressed multiplier. -/
theorem causalGenerator_analyticCore (u : rawComplexEntireCore) :
    causalGenerator (causalAnalyticCoreDomainMap u) = causalAnalyticCoreHierarchy 1 0 u :=
  (causalGenerator_eq_iff _ _).2 (causalAnalyticCoreEmbedding_hasRightDeriv u)

/-- The actual maximal generator violates every proposed bound in the original data norm. -/
theorem causalGenerator_unbounded_growth (B : ℝ) :
    ∃ u : causalGeneratorDomain, B * ‖u.val‖ < ‖causalGenerator u‖ := by
  by_contra h
  push Not at h
  have hb : ∀ u : rawComplexEntireCore,
      ‖rawComplexCauchyCoreHierarchy 1 0 u‖ ≤ max B 0 * ‖u‖ := by
    intro u
    have hu := h (causalAnalyticCoreDomainMap u)
    rw [causalGenerator_analyticCore] at hu
    change ‖rawComplexCauchyCoreHierarchy 1 0 u‖ ≤ B * ‖negativeCauchy u.val‖ at hu
    exact hu.trans ((mul_le_mul_of_nonneg_right (le_max_left B 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (negativeCauchy_bound u.val) (le_max_right B 0)))
  have hz := ((rawComplexCauchyCoreHierarchy_bounded_iff 1 0).1 ⟨max B 0,hb⟩).1
  exact Nat.one_ne_zero hz

/-- The maximal generator is discontinuous for the inherited L² input norm. -/
theorem causalGenerator_not_continuous : ¬ Continuous causalGenerator := by
  intro hc
  let T : causalGeneratorDomain →L[ℂ] hardyL2ᗮ := ⟨causalGenerator,hc⟩
  obtain ⟨u,hu⟩ := causalGenerator_unbounded_growth ‖T‖
  exact not_lt_of_ge (T.le_opNorm u) hu

end
end RHTower.FokasLenells
