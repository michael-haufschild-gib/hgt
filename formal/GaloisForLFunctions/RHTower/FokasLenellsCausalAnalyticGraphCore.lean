import GaloisForLFunctions.RHTower.FokasLenellsCausalResolvent
import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorCore

/-!
# The encoded analytic subspace is a core for the full maximal generator

The analytic graph is semigroup invariant. Its closure contains damped graph
integrals, hence graph resolvents of all analytic inputs. Input density and
continuity of the graph resolvent extend this to every completed datum. Since
the graph resolvent is onto, analytic input/derivative pairs approximate every
pair in the actual maximal graph, simultaneously in both original norms.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace causalGeneratorGraph := isClosed_causalGeneratorGraph.completeSpace_coe

/-- The actual encoded analytic input and its actual first derivative, in the maximal graph. -/
def causalAnalyticGraphMap : rawComplexEntireCore →ₗ[ℂ] causalGeneratorGraph where
  toFun u := ⟨(causalAnalyticCoreEmbedding u,causalAnalyticCoreHierarchy 1 0 u),
    (causalGeneratorGraph_mem_iff _ _).2 (causalAnalyticCoreEmbedding_hasRightDeriv u)⟩
  map_add' u v := by apply Subtype.ext; apply Prod.ext <;> exact map_add _ _ _
  map_smul' c u := by apply Subtype.ext; apply Prod.ext <;> exact map_smul _ _ _

/-- Actual graph evolution preserves the encoded analytic input/derivative pairs. -/
theorem causalAnalyticGraphMap_evolution (t : ℝ≥0) (u : rawComplexEntireCore) :
    causalGeneratorGraphEvolution t (causalAnalyticGraphMap u) =
      causalAnalyticGraphMap (rawComplexCoreHierarchy 0 ((t:ℝ):ℂ) u) := by
  apply Subtype.ext
  apply Prod.ext
  · exact causalAnalyticCoreEmbedding_evolution t u
  · change causalLowerCauchyEvolution t (causalAnalyticCoreEmbedding (rawComplexCoreHierarchy 1 0 u)) =
      causalAnalyticCoreEmbedding (rawComplexCoreHierarchy 1 0 (rawComplexCoreHierarchy 0 ((t:ℝ):ℂ) u))
    rw [causalAnalyticCoreEmbedding_evolution]
    change causalAnalyticCoreEmbedding (rawComplexCoreHierarchy 0 ((t:ℝ):ℂ) (rawComplexCoreHierarchy 1 0 u)) = _
    rw [rawComplexCoreHierarchy_comp,rawComplexCoreHierarchy_comp]
    simp only [zero_add,add_zero]

private def graphResolventLinear (a : ℝ) : hardyL2ᗮ →ₗ[ℂ] causalGeneratorGraph where
  toFun u := ⟨(causalLaplaceIntegral a u,Real.exp a • causalLaplaceIntegral a u-u),
    causalLaplaceIntegral_full_generator_pair a u⟩
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_add _ _ _
    · change Real.exp a • causalLaplaceIntegral a (u+v)-(u+v) =
        (Real.exp a • causalLaplaceIntegral a u-u)+(Real.exp a • causalLaplaceIntegral a v-v)
      rw [map_add,smul_add]
      abel
  map_smul' c u := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_smul _ _ _
    · change Real.exp a • causalLaplaceIntegral a (c • u)-c • u =
        c • (Real.exp a • causalLaplaceIntegral a u-u)
      rw [map_smul,smul_comm,smul_sub]

/-- The actual positive resolvent, continuous into the full maximal graph norm. -/
def causalResolventGraph (a : ℝ) : hardyL2ᗮ →L[ℂ] causalGeneratorGraph :=
  ⟨graphResolventLinear a,by
    apply continuous_induced_rng.2
    change Continuous (fun u : hardyL2ᗮ =>
      (causalLaplaceIntegral a u,Real.exp a • causalLaplaceIntegral a u-u))
    exact (causalLaplaceIntegral a).continuous.prodMk
      (((causalLaplaceIntegral a).continuous.const_smul (Real.exp a)).sub continuous_id)⟩

/-- Every actual input/derivative graph pair is the graph resolvent of a completed datum. -/
theorem causalResolventGraph_surjective (a : ℝ) : Function.Surjective (causalResolventGraph a) := by
  intro p
  let u : causalGeneratorDomain := ⟨p.val.1,⟨p,rfl⟩⟩
  refine ⟨causalGeneratorShift a u,?_⟩
  apply causalGeneratorGraphInput_injective
  exact congrArg (fun v : causalGeneratorDomain => v.val) (causalResolvent_generatorShift a u)

private def analyticGraphClosure : Submodule ℂ causalGeneratorGraph :=
  causalAnalyticGraphMap.range.topologicalClosure

private theorem analytic_graph_laplace_mem (a : ℝ) (u : rawComplexEntireCore) :
    causalGraphLaplaceIntegral a (causalAnalyticGraphMap u) ∈ analyticGraphClosure := by
  letI : CompleteSpace analyticGraphClosure := causalAnalyticGraphMap.range.isClosed_topologicalClosure.completeSpace_coe
  have hm (r : ℝ) : Real.exp (-Real.exp a*r) •
      causalGeneratorGraphEvolution r.toNNReal (causalAnalyticGraphMap u) ∈ analyticGraphClosure := by
    apply (analyticGraphClosure.restrictScalars ℝ).smul_mem
    apply causalAnalyticGraphMap.range.le_topologicalClosure
    exact ⟨rawComplexCoreHierarchy 0 ((r.toNNReal:ℝ):ℂ) u,
      (causalAnalyticGraphMap_evolution r.toNNReal u).symm⟩
  let f : ℝ → analyticGraphClosure := fun r =>
    ⟨Real.exp (-Real.exp a*r) • causalGeneratorGraphEvolution r.toNNReal (causalAnalyticGraphMap u),hm r⟩
  have he := LinearIsometry.integral_comp_comm (𝕜 := ℂ) (E := analyticGraphClosure)
    (F := causalGeneratorGraph) (μ := volume.restrict (Ioi (0:ℝ))) analyticGraphClosure.subtypeₗᵢ f
  change causalGraphLaplaceIntegral a (causalAnalyticGraphMap u) =
    (∫ r in Ioi (0:ℝ), f r).val at he
  rw [he]
  exact (∫ r in Ioi (0:ℝ), f r).property

/-- Encoded analytic data approximate every maximal generator pair in both state and derivative norm. -/
theorem causalAnalyticGraphMap_denseRange : DenseRange causalAnalyticGraphMap := by
  have hc : IsClosed {v : hardyL2ᗮ | causalResolventGraph 0 v ∈ analyticGraphClosure} :=
    causalAnalyticGraphMap.range.isClosed_topologicalClosure.preimage (causalResolventGraph 0).continuous
  have hs : Set.range causalAnalyticCoreEmbedding ⊆
      {v : hardyL2ᗮ | causalResolventGraph 0 v ∈ analyticGraphClosure} := by
    rintro v ⟨u,rfl⟩
    have he : causalResolventGraph 0 (causalAnalyticCoreEmbedding u) =
        causalGraphLaplaceIntegral 0 (causalAnalyticGraphMap u) := by
      apply causalGeneratorGraphInput_injective
      rw [causalGraphLaplaceIntegral_input]
      rfl
    change causalResolventGraph 0 (causalAnalyticCoreEmbedding u) ∈ analyticGraphClosure
    rw [he]
    exact analytic_graph_laplace_mem 0 u
  intro p
  change p ∈ analyticGraphClosure
  obtain ⟨v,rfl⟩ := causalResolventGraph_surjective 0 p
  exact (closure_minimal hs hc) (causalAnalyticCoreEmbedding_denseRange v)

end
end RHTower.FokasLenells
