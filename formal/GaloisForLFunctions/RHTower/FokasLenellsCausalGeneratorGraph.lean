import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorCriterion
import GaloisForLFunctions.RHTower.FokasLenellsCausalIntegratedSemigroup
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Closed maximal generator graph for actual causal Cauchy evolution

The graph is defined by actual finite-time orbit identities and proved equal
to the full right-derivative graph. Its input projection is injective, and
time averages prove dense domain. The resulting unbounded linear operator
therefore has its actual maximal domain, not a stipulated regularity class.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance fokasLenellsCausalGeneratorGraphInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- The actual integrated graph of causal evolution on the completed lower Hardy space. -/
def causalGeneratorGraph : Submodule ℂ ((hardyL2ᗮ) × (hardyL2ᗮ)) where
  carrier := {p | ∀ t : ℝ≥0, causalLowerCauchyEvolution t p.1-p.1 = causalOrbitIntegral t p.2}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro p q hp hq t
    change causalLowerCauchyEvolution t (p.1+q.1)-(p.1+q.1) = causalOrbitIntegral t (p.2+q.2)
    rw [map_add,map_add,← hp t,← hq t]
    abel
  smul_mem' := by
    intro c p hp t
    change causalLowerCauchyEvolution t (c • p.1)-c • p.1 = causalOrbitIntegral t (c • p.2)
    rw [map_smul,map_smul,← smul_sub,hp t]

/-- The integrated graph is exactly the complete actual right-derivative graph. -/
theorem causalGeneratorGraph_mem_iff (u v : hardyL2ᗮ) :
    (u,v) ∈ causalGeneratorGraph ↔ HasDerivWithinAt (causalForwardOrbit u) v (Ioi 0) 0 :=
  (causalForwardOrbit_rightDerivative_iff u v).symm

/-- The actual maximal generator graph is closed in the original product Hilbert topology. -/
theorem isClosed_causalGeneratorGraph : IsClosed (causalGeneratorGraph : Set ((hardyL2ᗮ) × (hardyL2ᗮ))) := by
  change IsClosed {p : (hardyL2ᗮ) × (hardyL2ᗮ) | ∀ t : ℝ≥0,
    causalLowerCauchyEvolution t p.1-p.1 = causalOrbitIntegral t p.2}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro t
  exact isClosed_eq (((causalLowerCauchyEvolution t).continuous.comp continuous_fst).sub continuous_fst)
    ((causalOrbitIntegral t).continuous.comp continuous_snd)

/-- The literal input projection of the closed graph. -/
def causalGeneratorGraphInput : causalGeneratorGraph →L[ℂ] hardyL2ᗮ :=
  (ContinuousLinearMap.fst ℂ (hardyL2ᗮ) (hardyL2ᗮ)).comp causalGeneratorGraph.subtypeL

/-- The literal derivative-output projection of the closed graph. -/
def causalGeneratorGraphOutput : causalGeneratorGraph →L[ℂ] hardyL2ᗮ :=
  (ContinuousLinearMap.snd ℂ (hardyL2ᗮ) (hardyL2ᗮ)).comp causalGeneratorGraph.subtypeL

/-- The actual graph has only one derivative output for each input. -/
theorem causalGeneratorGraphInput_injective : Function.Injective causalGeneratorGraphInput := by
  intro p q h
  change p.val.1 = q.val.1 at h
  have hp := (causalGeneratorGraph_mem_iff p.val.1 p.val.2).1 p.property
  have hq := (causalGeneratorGraph_mem_iff q.val.1 q.val.2).1 q.property
  rw [h] at hp
  apply Subtype.ext
  apply Prod.ext h
  exact (hp.derivWithin (uniqueDiffWithinAt_Ioi 0)).symm.trans
    (hq.derivWithin (uniqueDiffWithinAt_Ioi 0))

/-- The actual maximal generator domain, as the input range of the proved graph. -/
def causalGeneratorDomain : Submodule ℂ (hardyL2ᗮ) := causalGeneratorGraphInput.toLinearMap.range

/-- Every finite-time vector average has its exact actual generator output. -/
theorem causalGeneratorGraph_orbitIntegral (t : ℝ≥0) (u : hardyL2ᗮ) :
    (causalOrbitIntegral t u,causalLowerCauchyEvolution t u-u) ∈ causalGeneratorGraph := by
  intro s
  exact (causalOrbitIntegral_exchange s t u).symm

/-- Time-averaging proves density of the actual maximal generator domain. -/
theorem dense_causalGeneratorDomain : Dense (causalGeneratorDomain : Set (hardyL2ᗮ)) := by
  intro u
  apply mem_closure_of_tendsto (causalOrbitPrimitive_average_tendsto u)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  filter_upwards [hpos] with r hr
  have hi : causalOrbitIntegral r.toNNReal u ∈ causalGeneratorDomain :=
    ⟨⟨(causalOrbitIntegral r.toNNReal u,causalLowerCauchyEvolution r.toNNReal u-u),
      causalGeneratorGraph_orbitIntegral r.toNNReal u⟩,rfl⟩
  have he : causalOrbitPrimitive r u = causalOrbitIntegral r.toNNReal u := by
    change causalOrbitPrimitive r u = causalOrbitPrimitive (r.toNNReal:ℝ) u
    rw [Real.coe_toNNReal r hr.le]
  change r⁻¹ • causalOrbitPrimitive r u ∈ causalGeneratorDomain
  rw [he]
  exact (causalGeneratorDomain.restrictScalars ℝ).smul_mem r⁻¹ hi

/-- Domain membership is exactly existence of the actual right derivative, with no extra condition. -/
theorem causalGeneratorDomain_mem_iff (u : hardyL2ᗮ) :
    u ∈ causalGeneratorDomain ↔ ∃ v : hardyL2ᗮ, HasDerivWithinAt (causalForwardOrbit u) v (Ioi 0) 0 := by
  constructor
  · rintro ⟨p,hp⟩
    change p.val.1 = u at hp
    refine ⟨p.val.2,?_⟩
    rw [← hp]
    exact (causalGeneratorGraph_mem_iff _ _).1 p.property
  · rintro ⟨v,hv⟩
    exact ⟨⟨(u,v),(causalGeneratorGraph_mem_iff u v).2 hv⟩,rfl⟩

private def generatorInputEquiv : causalGeneratorGraph ≃ₗ[ℂ] causalGeneratorDomain :=
  LinearEquiv.ofInjective causalGeneratorGraphInput.toLinearMap causalGeneratorGraphInput_injective

/-- The actual unbounded infinitesimal generator on its proved maximal domain. -/
def causalGenerator : causalGeneratorDomain →ₗ[ℂ] hardyL2ᗮ :=
  causalGeneratorGraphOutput.toLinearMap.comp generatorInputEquiv.symm.toLinearMap

/-- The constructed maximal-domain operator is the actual right derivative on every input. -/
theorem causalGenerator_hasRightDeriv (u : causalGeneratorDomain) :
    HasDerivWithinAt (causalForwardOrbit u.val) (causalGenerator u) (Ioi 0) 0 := by
  let p : causalGeneratorGraph := generatorInputEquiv.symm u
  have hi := congrArg (fun v : causalGeneratorDomain => v.val) (generatorInputEquiv.apply_symm_apply u)
  change p.val.1 = u.val at hi
  have hd := (causalGeneratorGraph_mem_iff p.val.1 p.val.2).1 p.property
  rw [hi] at hd
  exact hd

/-- The actual generator output is uniquely characterized by the right derivative. -/
theorem causalGenerator_eq_iff (u : causalGeneratorDomain) (v : hardyL2ᗮ) :
    causalGenerator u = v ↔ HasDerivWithinAt (causalForwardOrbit u.val) v (Ioi 0) 0 := by
  constructor
  · rintro rfl
    exact causalGenerator_hasRightDeriv u
  · intro hv
    exact ((causalGenerator_hasRightDeriv u).derivWithin (uniqueDiffWithinAt_Ioi 0)).symm.trans
      (hv.derivWithin (uniqueDiffWithinAt_Ioi 0))

end
end RHTower.FokasLenells
