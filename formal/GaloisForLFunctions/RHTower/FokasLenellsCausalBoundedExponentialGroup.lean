import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedBoundaryChains
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedEntireIdentification

/-! Complex group laws and positive-time contraction in the genuine bounded derivative-chain norm. -/
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

local instance : NormedAlgebra ℚ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  .restrictScalars ℚ ℂ _

/-- The actual bounded derivative-shift exponential obeys the complex additive group law. -/
theorem causalBoundedChainExponential_add (z w : ℂ) :
    causalBoundedChainExponential (z+w) =
      causalBoundedChainExponential z * causalBoundedChainExponential w := by
  have ha : (z+w) • causalBoundedChainShift =
      z • causalBoundedChainShift + w • causalBoundedChainShift := add_smul _ _ _
  exact (congrArg (NormedSpace.exp : (causalBoundedChain →L[ℂ] causalBoundedChain) →
    (causalBoundedChain →L[ℂ] causalBoundedChain)) ha).trans
    (NormedSpace.exp_add_of_commute
      (((Commute.refl causalBoundedChainShift).smul_left z).smul_right w))

/-- Complex-time composition is literal composition on the actual bounded derivative chains. -/
theorem causalBoundedChainExponential_add_apply (z w : ℂ) (u : causalBoundedChain) :
    causalBoundedChainExponential (z+w) u =
      causalBoundedChainExponential z (causalBoundedChainExponential w u) :=
  congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (causalBoundedChainExponential_add z w)

/-- Reversing complex time recovers every genuine bounded derivative chain. -/
theorem causalBoundedChainExponential_neg_apply (z : ℂ) (u : causalBoundedChain) :
    causalBoundedChainExponential (-z) (causalBoundedChainExponential z u) = u := by
  have h := causalBoundedChainExponential_add_apply (-z) z u
  have hz : causalBoundedChainExponential 0 u = u :=
    congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
      causalBoundedChainExponential_zero
  have hs : causalBoundedChainExponential (-z+z) u = u :=
    (congrArg (fun q : ℂ => causalBoundedChainExponential q u) (neg_add_cancel z)).trans hz
  exact h.symm.trans hs

/-- The opposite complex-time composition also recovers the same actual chain. -/
theorem causalBoundedChainExponential_apply_neg (z : ℂ) (u : causalBoundedChain) :
    causalBoundedChainExponential z (causalBoundedChainExponential (-z) u) = u := by
  have h := causalBoundedChainExponential_neg_apply (-z) u
  simpa only [neg_neg] using h

/-- The genuine entire evolution is a continuous linear automorphism at every complex time. -/
def causalBoundedEntireGroup (z : ℂ) : causalBoundedChain ≃L[ℂ] causalBoundedChain where
  toLinearMap := (causalBoundedChainExponential z).toLinearMap
  invFun := causalBoundedChainExponential (-z)
  left_inv := causalBoundedChainExponential_neg_apply z
  right_inv := causalBoundedChainExponential_apply_neg z
  continuous_toFun := (causalBoundedChainExponential z).continuous
  continuous_invFun := (causalBoundedChainExponential (-z)).continuous

/-- The actual entire operator has both injectivity and surjectivity on the stronger chain space. -/
theorem causalBoundedChainExponential_bijective (z : ℂ) :
    Function.Bijective (causalBoundedChainExponential z) := (causalBoundedEntireGroup z).bijective

/-- Positive real time contracts every derivative simultaneously in the actual supremum norm. -/
theorem causalBoundedChainExponential_real_norm_le (t : ℝ≥0) (u : causalBoundedChain) :
    ‖causalBoundedChainExponential ((t : ℝ) : ℂ) u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg u)
  intro j
  change ‖causalBoundedEntireOrbit j u ((t : ℝ) : ℂ)‖ ≤ ‖u‖
  have h := congrArg (fun v : hardyL2ᗮ => ‖v‖) (causalBoundedEntireOrbit_eq_evolution j u t)
  exact h.trans_le ((causalLowerCauchyEvolution_norm_le t _).trans
    (causalBoundedChainCoordinate_norm_le j u))

/-- Actual positive-time contraction is sharp in the genuine bounded-all-derivatives norm. -/
theorem norm_causalBoundedChainExponential_real (t : ℝ≥0) :
    ‖causalBoundedChainExponential ((t : ℝ) : ℂ)‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun u => by simpa only [one_mul] using causalBoundedChainExponential_real_norm_le t u)
  · have hb : ‖causalBoundedChainOrbit t‖ ≤ ‖causalBoundedChainExponential ((t : ℝ) : ℂ)‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      have he : ‖causalBoundedChainOrbit t u‖ =
          ‖causalBoundedChainCoordinate 0 (causalBoundedChainExponential ((t : ℝ) : ℂ) u)‖ :=
        (congrArg (fun v : hardyL2ᗮ => ‖v‖) (causalBoundedEntireOrbit_eq_evolution 0 u t)).symm
      exact he.trans_le ((causalBoundedChainCoordinate_norm_le 0 _).trans
        ((causalBoundedChainExponential ((t : ℝ) : ℂ)).le_opNorm u))
    exact (norm_causalBoundedChainOrbit t).symm.trans_le hb

end
end RHTower.FokasLenells
