import GaloisForLFunctions.RHTower.FokasLenellsCausalSmoothBoundaryChains
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Genuine infinite generator chains with uniformly bounded derivative norms.
The inherited infinity-sequence norm makes this actual closed carrier a Banach space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance fokasLenellsCausalBoundedChainInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Actual bounded sequences whose consecutive coordinates lie in the maximal-generator graph. -/
def causalBoundedChain : Submodule ℂ (lp (fun _ : ℕ => hardyL2ᗮ) ∞) :=
  ⨅ j : ℕ, causalGeneratorGraph.comap
    ((lp.evalₗ (fun _ : ℕ => hardyL2ᗮ) ∞ j).prod
      (lp.evalₗ (fun _ : ℕ => hardyL2ᗮ) ∞ (j+1)))

/-- Membership imposes the genuine generator equation at every consecutive coordinate. -/
theorem causalBoundedChain_mem_iff (v : lp (fun _ : ℕ => hardyL2ᗮ) ∞) :
    v ∈ causalBoundedChain ↔ ∀ j : ℕ, (v j, v (j+1)) ∈ causalGeneratorGraph := by
  simp only [causalBoundedChain, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

/-- The genuine bounded-chain carrier is closed in the actual infinity-sequence norm. -/
theorem isClosed_causalBoundedChain :
    IsClosed (causalBoundedChain : Set (lp (fun _ : ℕ => hardyL2ᗮ) ∞)) := by
  have he : (causalBoundedChain : Set (lp (fun _ : ℕ => hardyL2ᗮ) ∞)) =
      {v | ∀ j : ℕ, (v j, v (j+1)) ∈ causalGeneratorGraph} :=
    Set.ext causalBoundedChain_mem_iff
  rw [he]
  simp only [setOf_forall]
  exact isClosed_iInter (fun j => isClosed_causalGeneratorGraph.preimage
    ((lp.evalCLM ℂ (fun _ : ℕ => hardyL2ᗮ) ∞ j).continuous.prodMk
      (lp.evalCLM ℂ (fun _ : ℕ => hardyL2ᗮ) ∞ (j+1)).continuous))

/-- The actual bounded-chain space is complete for its inherited norm. -/
theorem causalBoundedChain_complete : CompleteSpace causalBoundedChain :=
  isClosed_causalBoundedChain.completeSpace_coe

/-- A continuous coordinate of a genuine bounded derivative chain. -/
def causalBoundedChainCoordinate (j : ℕ) : causalBoundedChain →L[ℂ] hardyL2ᗮ :=
  (lp.evalCLM ℂ (fun _ : ℕ => hardyL2ᗮ) ∞ j).comp causalBoundedChain.subtypeL

/-- The same one chain norm bounds every genuine derivative coordinate. -/
theorem causalBoundedChainCoordinate_norm_le (j : ℕ) (u : causalBoundedChain) :
    ‖causalBoundedChainCoordinate j u‖ ≤ ‖u‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero u.val j

/-- Forgetting the stronger norm embeds actual bounded chains into the genuine smooth chain space. -/
def causalBoundedChainToSmooth : causalBoundedChain →L[ℂ] causalSmoothGraph where
  toLinearMap := {
    toFun := fun u => ⟨u.val, (causalSmoothGraph_mem_iff _).2
      ((causalBoundedChain_mem_iff _).1 u.property)⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  cont := continuous_induced_rng.2
    (continuous_pi (fun j => (causalBoundedChainCoordinate j).continuous))

/-- Forgetting the stronger chain norm does not change any coordinate. -/
theorem causalBoundedChainToSmooth_coordinate (j : ℕ) (u : causalBoundedChain) :
    causalSmoothGraphCoordinate j (causalBoundedChainToSmooth u) =
      causalBoundedChainCoordinate j u := rfl

/-- The initial datum uniquely determines the entire actual bounded derivative chain. -/
theorem causalBoundedChainCoordinate_zero_injective :
    Function.Injective (causalBoundedChainCoordinate 0) := by
  intro u v h
  have he : causalBoundedChainToSmooth u = causalBoundedChainToSmooth v :=
    causalSmoothGraphCoordinate_zero_injective h
  apply Subtype.ext
  apply lp.ext
  exact congrArg (fun w : causalSmoothGraph => w.val) he

/-- Every coordinate of a genuine bounded chain belongs to every finite generator domain. -/
theorem causalBoundedChainCoordinate_mem_powerDomain (j k : ℕ) (u : causalBoundedChain) :
    causalBoundedChainCoordinate j u ∈ causalGeneratorPowerDomain k :=
  causalSmoothGraphCoordinate_mem_powerDomain j k (causalBoundedChainToSmooth u)

/-- Each successor is the actual right derivative of the preceding coordinate's causal orbit. -/
theorem causalBoundedChainCoordinate_hasRightDeriv (j : ℕ) (u : causalBoundedChain) :
    HasDerivWithinAt (causalForwardOrbit (causalBoundedChainCoordinate j u))
      (causalBoundedChainCoordinate (j+1) u) (Ioi 0) 0 :=
  causalSmoothGraphCoordinate_hasRightDeriv j (causalBoundedChainToSmooth u)

private def boundedChainShiftLinear : causalBoundedChain →ₗ[ℂ] causalBoundedChain where
  toFun u := ⟨⟨fun j => u.val (j+1), memℓp_infty ⟨‖u‖, by
    rintro y ⟨j, rfl⟩
    exact causalBoundedChainCoordinate_norm_le (j+1) u⟩⟩,
    (causalBoundedChain_mem_iff _).2 (fun j =>
      (causalBoundedChain_mem_iff _).1 u.property (j+1))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual derivative shift is a bounded endomorphism on the complete bounded-chain space. -/
def causalBoundedChainShift : causalBoundedChain →L[ℂ] causalBoundedChain :=
  boundedChainShiftLinear.mkContinuous 1 (fun u => by
    change ‖(boundedChainShiftLinear u).val‖ ≤ 1*‖u‖
    rw [one_mul]
    exact lp.norm_le_of_forall_le (norm_nonneg u)
      (fun j => causalBoundedChainCoordinate_norm_le (j+1) u))

/-- The bounded endomorphism is the literal shift of genuine derivatives. -/
theorem causalBoundedChainShift_coordinate (j : ℕ) (u : causalBoundedChain) :
    causalBoundedChainCoordinate j (causalBoundedChainShift u) =
      causalBoundedChainCoordinate (j+1) u := rfl

/-- Taking one actual derivative cannot increase the bounded-chain norm. -/
theorem causalBoundedChainShift_norm_le (u : causalBoundedChain) :
    ‖causalBoundedChainShift u‖ ≤ ‖u‖ :=
  lp.norm_le_of_forall_le (norm_nonneg u)
    (fun j => causalBoundedChainCoordinate_norm_le (j+1) u)

/-- The genuine derivative shift has operator norm at most one. -/
theorem norm_causalBoundedChainShift_le : ‖causalBoundedChainShift‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun u => by simpa only [one_mul] using causalBoundedChainShift_norm_le u)

end
end RHTower.FokasLenells
