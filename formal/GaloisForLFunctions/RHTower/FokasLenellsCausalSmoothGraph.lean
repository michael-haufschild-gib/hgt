import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorPowerDomains

/-! The actual space of infinite derivative chains for the maximal causal generator.
Successive coordinates belong to its proved closed graph, with the inherited product topology. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance fokasLenellsCausalSmoothGraphInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Infinite chains of genuine maximal-generator pairs, in the original countable product space. -/
def causalSmoothGraph : Submodule ℂ (ℕ → hardyL2ᗮ) :=
  ⨅ j : ℕ, causalGeneratorGraph.comap
    ((LinearMap.proj j : (ℕ → hardyL2ᗮ) →ₗ[ℂ] hardyL2ᗮ).prod (LinearMap.proj (j+1)))

/-- Membership means exactly that every consecutive pair lies in the genuine generator graph. -/
theorem causalSmoothGraph_mem_iff (v : ℕ → hardyL2ᗮ) :
    v ∈ causalSmoothGraph ↔ ∀ j : ℕ, (v j, v (j+1)) ∈ causalGeneratorGraph := by
  simp only [causalSmoothGraph, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

/-- The genuine infinite-chain space is closed in the product of the actual Hilbert spaces. -/
theorem isClosed_causalSmoothGraph : IsClosed (causalSmoothGraph : Set (ℕ → hardyL2ᗮ)) := by
  have he : (causalSmoothGraph : Set (ℕ → hardyL2ᗮ)) =
      {v : ℕ → hardyL2ᗮ | ∀ j : ℕ, (v j, v (j+1)) ∈ causalGeneratorGraph} :=
    Set.ext causalSmoothGraph_mem_iff
  rw [he]
  simp only [setOf_forall]
  exact isClosed_iInter (fun j => isClosed_causalGeneratorGraph.preimage
    ((continuous_apply j).prodMk (continuous_apply (j+1))))

/-- Closedness makes the actual countable chain space complete in its inherited uniformity. -/
theorem causalSmoothGraph_complete : CompleteSpace causalSmoothGraph :=
  isClosed_causalSmoothGraph.completeSpace_coe

/-- A continuous coordinate readout of a genuine infinite generator chain. -/
def causalSmoothGraphCoordinate (j : ℕ) : causalSmoothGraph →L[ℂ] hardyL2ᗮ where
  toLinearMap := (LinearMap.proj j).comp causalSmoothGraph.subtype
  cont := (continuous_apply j).comp continuous_subtype_val

/-- Every consecutive coordinate pair records the actual right derivative of its causal orbit. -/
theorem causalSmoothGraphCoordinate_hasRightDeriv (j : ℕ) (u : causalSmoothGraph) :
    HasDerivWithinAt (causalForwardOrbit (causalSmoothGraphCoordinate j u))
      (causalSmoothGraphCoordinate (j+1) u) (Ioi 0) 0 :=
  (causalGeneratorGraph_mem_iff _ _).1 ((causalSmoothGraph_mem_iff u.val).1 u.property j)

/-- Every coordinate is an element of the genuine maximal-generator domain. -/
def causalSmoothGraphDomainCoordinate (j : ℕ) (u : causalSmoothGraph) : causalGeneratorDomain :=
  ⟨causalSmoothGraphCoordinate j u, (causalGeneratorDomain_mem_iff _).2
    ⟨causalSmoothGraphCoordinate (j+1) u, causalSmoothGraphCoordinate_hasRightDeriv j u⟩⟩

/-- The actual maximal generator sends each coordinate to its literal successor. -/
theorem causalGenerator_smoothGraphCoordinate (j : ℕ) (u : causalSmoothGraph) :
    causalGenerator (causalSmoothGraphDomainCoordinate j u) = causalSmoothGraphCoordinate (j+1) u :=
  (causalGenerator_eq_iff _ _).2 (causalSmoothGraphCoordinate_hasRightDeriv j u)

/-- No two genuine infinite derivative chains have the same initial datum. -/
theorem causalSmoothGraphCoordinate_zero_injective :
    Function.Injective (causalSmoothGraphCoordinate 0) := by
  intro u v h
  apply Subtype.ext
  funext j
  induction j with
  | zero => exact h
  | succ j ih =>
    have hp : (⟨(u.val j, u.val (j+1)), (causalSmoothGraph_mem_iff u.val).1 u.property j⟩ : causalGeneratorGraph) =
        ⟨(v.val j, v.val (j+1)), (causalSmoothGraph_mem_iff v.val).1 v.property j⟩ := by
      apply causalGeneratorGraphInput_injective
      exact ih
    exact congrArg (fun p : causalGeneratorGraph => p.val.2) hp

/-- Every coordinate of a genuine infinite chain belongs to every finite generator domain. -/
theorem causalSmoothGraphCoordinate_mem_powerDomain (j k : ℕ) (u : causalSmoothGraph) :
    causalSmoothGraphCoordinate j u ∈ causalGeneratorPowerDomain k := by
  induction k generalizing j with
  | zero => exact Submodule.mem_top
  | succ k ih =>
    refine ⟨causalSmoothGraphDomainCoordinate j u, ?_, rfl⟩
    change causalGenerator (causalSmoothGraphDomainCoordinate j u) ∈ causalGeneratorPowerDomain k
    rw [causalGenerator_smoothGraphCoordinate]
    exact ih (j+1)

end
end RHTower.FokasLenells
