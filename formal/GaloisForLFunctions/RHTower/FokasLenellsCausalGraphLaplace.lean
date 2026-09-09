import GaloisForLFunctions.RHTower.FokasLenellsCausalGraphEvolution
import GaloisForLFunctions.RHTower.FokasLenellsCausalLaplaceIntegral

/-!
# Laplace integration in the actual closed generator graph

The graph is complete and its vector orbits contract. Bochner integration in
that graph proves domain preservation and commutation with the actual
unbounded generator. Both graph projections are bounded maps, so neither
interchange requires a bounded generator on the original input space.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace causalGeneratorGraph := isClosed_causalGeneratorGraph.completeSpace_coe
local instance : SecondCountableTopologyEither ℝ causalGeneratorGraph :=
  secondCountableTopologyEither_of_left ℝ causalGeneratorGraph

private def graphLaplaceOrbit (a : ℝ) (p : causalGeneratorGraph) (r : ℝ) : causalGeneratorGraph :=
  Real.exp (-Real.exp a*r) • causalGeneratorGraphEvolution r.toNNReal p

private theorem graphLaplaceOrbit_integrable (a : ℝ) (p : causalGeneratorGraph) :
    IntegrableOn (graphLaplaceOrbit a p) (Ioi (0:ℝ)) volume := by
  have hc : Continuous (graphLaplaceOrbit a p) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((causalGeneratorGraphEvolution_continuous p).comp continuous_real_toNNReal)
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos (Real.exp_pos a)) 0).mul_const ‖p‖
  apply Integrable.mono' hi hc.aestronglyMeasurable.restrict
  apply Eventually.of_forall
  intro r
  rw [graphLaplaceOrbit,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (causalGeneratorGraphEvolution_norm_le r.toNNReal p) (Real.exp_pos _).le

/-- The actual vector Laplace integral taken in the complete maximal generator graph. -/
def causalGraphLaplaceIntegral (a : ℝ) (p : causalGeneratorGraph) : causalGeneratorGraph :=
  ∫ r in Ioi (0:ℝ), graphLaplaceOrbit a p r

/-- Integrating in the graph has precisely the original vector Laplace integral as input. -/
theorem causalGraphLaplaceIntegral_input (a : ℝ) (p : causalGeneratorGraph) :
    causalGeneratorGraphInput (causalGraphLaplaceIntegral a p) =
      causalLaplaceIntegral a (causalGeneratorGraphInput p) := by
  rw [causalGraphLaplaceIntegral,causalLaplaceIntegral_apply]
  have hc := (causalGeneratorGraphInput.restrictScalars ℝ).integral_comp_comm (graphLaplaceOrbit_integrable a p)
  change (∫ r in Ioi (0:ℝ), causalGeneratorGraphInput (graphLaplaceOrbit a p r)) =
    causalGeneratorGraphInput (∫ r in Ioi (0:ℝ), graphLaplaceOrbit a p r) at hc
  rw [← hc]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  change causalGeneratorGraphInput (Real.exp (-Real.exp a*r) • causalGeneratorGraphEvolution r.toNNReal p) = _
  rw [ContinuousLinearMap.map_smul_of_tower,causalGeneratorGraphEvolution_input]
  rfl

/-- The integrated graph output is the Laplace integral of the actual derivative output. -/
theorem causalGraphLaplaceIntegral_output (a : ℝ) (p : causalGeneratorGraph) :
    causalGeneratorGraphOutput (causalGraphLaplaceIntegral a p) =
      causalLaplaceIntegral a (causalGeneratorGraphOutput p) := by
  rw [causalGraphLaplaceIntegral,causalLaplaceIntegral_apply]
  have hc := (causalGeneratorGraphOutput.restrictScalars ℝ).integral_comp_comm (graphLaplaceOrbit_integrable a p)
  change (∫ r in Ioi (0:ℝ), causalGeneratorGraphOutput (graphLaplaceOrbit a p r)) =
    causalGeneratorGraphOutput (∫ r in Ioi (0:ℝ), graphLaplaceOrbit a p r) at hc
  rw [← hc]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  change causalGeneratorGraphOutput (Real.exp (-Real.exp a*r) • causalGeneratorGraphEvolution r.toNNReal p) = _
  rw [ContinuousLinearMap.map_smul_of_tower,causalGeneratorGraphEvolution_output]
  rfl

/-- Laplace integration preserves actual input/derivative pairs in the maximal closed graph. -/
theorem causalLaplaceIntegral_generator_pair (a : ℝ) (u : causalGeneratorDomain) :
    (causalLaplaceIntegral a u.val,causalLaplaceIntegral a (causalGenerator u)) ∈ causalGeneratorGraph := by
  let p : causalGeneratorGraph := ⟨(u.val,causalGenerator u),
    (causalGeneratorGraph_mem_iff _ _).2 (causalGenerator_hasRightDeriv u)⟩
  have hi := causalGraphLaplaceIntegral_input a p
  have ho := causalGraphLaplaceIntegral_output a p
  have he : (causalGraphLaplaceIntegral a p).val =
      (causalLaplaceIntegral a u.val,causalLaplaceIntegral a (causalGenerator u)) := Prod.ext hi ho
  have h := (causalGraphLaplaceIntegral a p).property
  rwa [he] at h

/-- The vector Laplace operator preserves the actual maximal generator domain. -/
theorem causalLaplaceIntegral_mem_domain (a : ℝ) (u : causalGeneratorDomain) :
    causalLaplaceIntegral a u.val ∈ causalGeneratorDomain :=
  ⟨⟨_,causalLaplaceIntegral_generator_pair a u⟩,rfl⟩

/-- The literal restriction of the vector Laplace operator to the maximal domain. -/
def causalLaplaceDomainMap (a : ℝ) : causalGeneratorDomain →ₗ[ℂ] causalGeneratorDomain :=
  ((causalLaplaceIntegral a).toLinearMap.comp causalGeneratorDomain.subtype).codRestrict causalGeneratorDomain
    (causalLaplaceIntegral_mem_domain a)

/-- The actual unbounded generator commutes with its vector Laplace integral on the full domain. -/
theorem causalGenerator_commutes_laplace (a : ℝ) (u : causalGeneratorDomain) :
    causalGenerator (causalLaplaceDomainMap a u) = causalLaplaceIntegral a (causalGenerator u) :=
  (causalGenerator_eq_iff _ _).2 ((causalGeneratorGraph_mem_iff _ _).1 (causalLaplaceIntegral_generator_pair a u))

end
end RHTower.FokasLenells
