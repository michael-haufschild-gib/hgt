import GaloisForLFunctions.RHTower.FokasLenellsCausalGraphLaplace
import GaloisForLFunctions.RHTower.FokasLenellsCausalLaplaceDerivative
import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorDissipation

/-!
# Actual positive resolvents of the maximal causal generator

The graph identity extends from dense domain inputs to every completed datum
by closedness of the actual generator graph. Thus each strictly positive
shift is onto as well as injective, and its actual inverse is exactly the
whole-ray vector Laplace integral with reciprocal damping control.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Every completed datum supplies its actual resolvent input/derivative pair in the closed graph. -/
theorem causalLaplaceIntegral_full_generator_pair (a : ℝ) (u : hardyL2ᗮ) :
    (causalLaplaceIntegral a u,Real.exp a • causalLaplaceIntegral a u-u) ∈ causalGeneratorGraph := by
  have hc : IsClosed {v : hardyL2ᗮ |
      (causalLaplaceIntegral a v,Real.exp a • causalLaplaceIntegral a v-v) ∈ causalGeneratorGraph} :=
    isClosed_causalGeneratorGraph.preimage ((causalLaplaceIntegral a).continuous.prodMk
      (((causalLaplaceIntegral a).continuous.const_smul (Real.exp a)).sub continuous_id))
  have hs : (causalGeneratorDomain : Set (hardyL2ᗮ)) ⊆
      {v | (causalLaplaceIntegral a v,Real.exp a • causalLaplaceIntegral a v-v) ∈ causalGeneratorGraph} := by
    intro v hv
    have h := causalLaplaceIntegral_generator_pair a ⟨v,hv⟩
    rw [causalLaplaceIntegral_generator_identity] at h
    exact h
  exact (closure_minimal hs hc) (dense_causalGeneratorDomain u)

/-- The actual Laplace integral sends every completed datum into the maximal generator domain. -/
theorem causalLaplaceIntegral_all_mem_domain (a : ℝ) (u : hardyL2ᗮ) :
    causalLaplaceIntegral a u ∈ causalGeneratorDomain :=
  ⟨⟨_,causalLaplaceIntegral_full_generator_pair a u⟩,rfl⟩

/-- The actual positive resolvent, with its proved maximal-domain codomain and inherited norm. -/
def causalResolvent (a : ℝ) : hardyL2ᗮ →L[ℂ] causalGeneratorDomain :=
  (causalLaplaceIntegral a).codRestrict causalGeneratorDomain (causalLaplaceIntegral_all_mem_domain a)

/-- The actual resolvent retains its whole-ray vector Laplace representation. -/
theorem causalResolvent_eq_laplace (a : ℝ) (u : hardyL2ᗮ) :
    (causalResolvent a u).val = causalLaplaceIntegral a u := rfl

/-- Applying the maximal generator to the resolvent gives the literal shifted equation. -/
theorem causalGenerator_resolvent (a : ℝ) (u : hardyL2ᗮ) :
    causalGenerator (causalResolvent a u) = Real.exp a • (causalResolvent a u).val-u :=
  (causalGenerator_eq_iff _ _).2 ((causalGeneratorGraph_mem_iff _ _).1
    (causalLaplaceIntegral_full_generator_pair a u))

/-- The actual resolvent is a right inverse for the positive generator shift on every datum. -/
theorem causalGeneratorShift_resolvent (a : ℝ) (u : hardyL2ᗮ) :
    causalGeneratorShift a (causalResolvent a u) = u := by
  change (algebraMap ℝ ℂ (Real.exp a)) • (causalResolvent a u).val-
    causalGenerator (causalResolvent a u) = u
  rw [algebraMap_smul,causalGenerator_resolvent]
  abel

/-- The actual resolvent is also a left inverse on the entire maximal generator domain. -/
theorem causalResolvent_generatorShift (a : ℝ) (u : causalGeneratorDomain) :
    causalResolvent a (causalGeneratorShift a u) = u := by
  apply causalGeneratorShift_injective a
  rw [causalGeneratorShift_resolvent]

/-- Every strictly positive shift of the actual maximal generator is onto. -/
theorem causalGeneratorShift_surjective (a : ℝ) : Function.Surjective (causalGeneratorShift a) :=
  fun u => ⟨causalResolvent a u,causalGeneratorShift_resolvent a u⟩

/-- The actual maximal-domain resolvent has the reciprocal positive-damping norm bound. -/
theorem causalResolvent_norm_le (a : ℝ) (u : hardyL2ᗮ) :
    ‖causalResolvent a u‖ ≤ (Real.exp a)⁻¹ * ‖u‖ := causalLaplaceIntegral_norm_le a u

/-- Actual positive resolvents satisfy the full difference identity on unchanged completed data. -/
theorem causalResolvent_identity (a b : ℝ) (u : hardyL2ᗮ) :
    causalResolvent a u-causalResolvent b u =
      (Real.exp b-Real.exp a) • causalResolvent a (causalResolvent b u).val := by
  apply causalGeneratorShift_injective a
  rw [map_sub,LinearMap.map_smul_of_tower,causalGeneratorShift_resolvent,causalGeneratorShift_resolvent]
  change u-((algebraMap ℝ ℂ (Real.exp a)) • (causalResolvent b u).val-
    causalGenerator (causalResolvent b u)) = _
  rw [algebraMap_smul,causalGenerator_resolvent]
  module

end
end RHTower.FokasLenells
