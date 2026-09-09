import GaloisForLFunctions.RHTower.FokasLenellsCausalRationalCoreSeparation

/-! Two explicit dense cores for the same maximal causal generator share only the zero graph pair. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Finite actual rational state/derivative pairs inside the maximal generator graph. -/
def causalRationalGraphCore : Submodule ℂ causalGeneratorGraph :=
  Submodule.span ℂ (Set.range causalCauchyEigenGraph)

/-- Actual encoded entire-core state/derivative pairs inside the same maximal generator graph. -/
def causalEncodedGraphCore : Submodule ℂ causalGeneratorGraph := causalAnalyticGraphMap.range

/-- Rational and encoded analytic generator graph cores intersect only at the zero graph pair. -/
theorem causalRationalGraphCore_inf_encoded_eq_bot :
    causalRationalGraphCore ⊓ causalEncodedGraphCore = ⊥ := by
  let Q : causalGeneratorGraph →ₗ[ℂ] SoninL2 :=
    (hardyL2ᗮ).subtype.comp causalGeneratorGraphInput.toLinearMap
  have hr : causalRationalGraphCore ≤ causalRationalCauchySpan.comap Q := by
    apply Submodule.span_le.mpr
    rintro p ⟨w, rfl⟩
    exact Submodule.subset_span ⟨w, rfl⟩
  apply bot_unique
  intro p hp
  have hrp : Q p ∈ causalRationalCauchySpan := hr hp.1
  have hep : Q p ∈ rawComplexCauchyCoreRange := by
    obtain ⟨u, hu⟩ := hp.2
    rw [← hu]
    exact ⟨u, rfl⟩
  have hz : Q p = 0 := by
    have h : Q p ∈ causalRationalCauchySpan ⊓ rawComplexCauchyCoreRange := ⟨hrp, hep⟩
    rw [causalRationalCauchySpan_inf_encoded_eq_bot] at h
    exact h
  change p = 0
  apply causalGeneratorGraphInput_injective
  apply Subtype.ext
  exact hz

/-- Two concrete approximation families are each dense in the full generator graph norm while
sharing only zero: rational Cauchy sums and encoded entire analytic data. -/
theorem causal_disjoint_dense_graph_cores :
    causalRationalGraphCore ⊓ causalEncodedGraphCore = ⊥ ∧
    causalRationalGraphCore.topologicalClosure = ⊤ ∧
    causalEncodedGraphCore.topologicalClosure = ⊤ := by
  refine ⟨causalRationalGraphCore_inf_encoded_eq_bot,
    topologicalClosure_span_causalCauchyEigenGraph_eq_top, ?_⟩
  apply top_unique
  intro p _
  change p ∈ closure (Set.range causalAnalyticGraphMap)
  exact causalAnalyticGraphMap_denseRange p

end
end RHTower.FokasLenells
