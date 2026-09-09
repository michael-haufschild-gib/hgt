import GaloisForLFunctions.RHTower.FokasLenellsCausalCauchySemigroup

/-!
# Actual adjoint and coisometry of causal Cauchy evolution

The completed causal operator has the literal opposite-time lower Hardy
isometry as adjoint. Forward evolution followed by this adjoint identity
gives exact isometric recovery, while the opposite composition retains only
the orthogonal recoverable part of the original datum.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Pairing against actual lower Hardy data removes the signed negative Cauchy projection. -/
theorem inner_negativeCauchy_lower (y : SoninL2) (u : hardyL2ᗮ) :
    inner ℂ (-negativeCauchy y) u.val = inner ℂ y u.val := by
  have hh : y + negativeCauchy y ∈ hardyL2 := by
    apply (negativeCauchy_eq_zero_iff _).1
    rw [map_add,negativeCauchy_square,add_neg_cancel]
  have hi := (Submodule.mem_orthogonal hardyL2 _).1 u.property _ hh
  rw [inner_add_left] at hi
  rw [inner_neg_left]
  exact (eq_neg_of_add_eq_zero_left hi).symm

/-- Literal opposite-time unitary evolution restricted to lower Hardy data. -/
def causalLowerRecovery (t : ℝ≥0) : hardyL2ᗮ →ₗᵢ[ℂ] hardyL2ᗮ where
  toLinearMap := ((evolution (-(t:ℝ))).toLinearEquiv.toLinearMap.comp
    (hardyL2ᗮ).subtype).codRestrict (hardyL2ᗮ) (evolution_nonpositive_mem_lowerHardy t)
  norm_map' u := norm_evolution (-(t:ℝ)) u.val

/-- The completed forward adjoint is exactly the original opposite-time lower Hardy isometry. -/
theorem causalLowerCauchyEvolution_adjoint (t : ℝ≥0) :
    (causalLowerCauchyEvolution t).adjoint = (causalLowerRecovery t).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (-negativeCauchy (evolution t v.val)) u.val =
    inner ℂ v.val (evolution (-(t:ℝ)) u.val)
  rw [inner_negativeCauchy_lower]
  have hi := (evolution (t:ℝ)).inner_map_map v.val (evolution (-(t:ℝ)) u.val)
  rw [← evolution_add,add_neg_cancel,evolution_zero] at hi
  exact hi

/-- The actual adjoint preserves every lower Hardy norm. -/
theorem norm_causalLowerCauchyEvolution_adjoint_apply (t : ℝ≥0) (u : hardyL2ᗮ) :
    ‖(causalLowerCauchyEvolution t).adjoint u‖ = ‖u‖ := by
  rw [causalLowerCauchyEvolution_adjoint]
  exact (causalLowerRecovery t).norm_map u

/-- The actual forward operator composed with its adjoint is the identity. -/
theorem causalLowerCauchyEvolution_comp_adjoint (t : ℝ≥0) :
    (causalLowerCauchyEvolution t).comp (causalLowerCauchyEvolution t).adjoint =
      ContinuousLinearMap.id ℂ (hardyL2ᗮ) := by
  rw [causalLowerCauchyEvolution_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change -negativeCauchy (evolution t (evolution (-(t:ℝ)) u.val)) = u.val
  rw [← evolution_add,add_neg_cancel,evolution_zero,(negativeCauchy_eq_neg_iff _).2 u.property,neg_neg]

/-- Every completed forward operator has the sharp operator norm one. -/
theorem norm_causalLowerCauchyEvolution (t : ℝ≥0) : ‖causalLowerCauchyEvolution t‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simpa only [one_mul] using causalLowerCauchyEvolution_norm_le t u
  · let u := causalCauchyKernelWitness 0
    have hu : 0 < ‖u‖ := norm_pos_iff.mpr (causalCauchyKernelWitness_ne_zero 0)
    have he := congrArg (fun T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ => T u)
      (causalLowerCauchyEvolution_comp_adjoint t)
    change causalLowerCauchyEvolution t ((causalLowerCauchyEvolution t).adjoint u) = u at he
    have hb := (causalLowerCauchyEvolution t).le_opNorm ((causalLowerCauchyEvolution t).adjoint u)
    rw [he,norm_causalLowerCauchyEvolution_adjoint_apply] at hb
    nlinarith

/-- The adjoint isometry also obeys the exact causal additive parameter law. -/
theorem causalLowerRecovery_add (s t : ℝ≥0) (u : hardyL2ᗮ) :
    causalLowerRecovery (s+t) u = causalLowerRecovery s (causalLowerRecovery t u) := by
  apply Subtype.ext
  change evolution (-((s:ℝ)+(t:ℝ))) u.val =
    evolution (-(s:ℝ)) (evolution (-(t:ℝ)) u.val)
  rw [neg_add,evolution_add]

/-- Each actual adjoint/recovery orbit is strongly continuous. -/
theorem causalLowerRecovery_continuous (u : hardyL2ᗮ) :
    Continuous (fun t : ℝ≥0 => causalLowerRecovery t u) := by
  apply continuous_induced_rng.2
  change Continuous (fun t : ℝ≥0 => evolution (-(t:ℝ)) u.val)
  exact (continuous_evolution_apply u.val).comp continuous_subtype_val.neg

/-- Reverse-time recovery is onto exactly at zero time. -/
theorem causalLowerRecovery_surjective_iff (t : ℝ≥0) : Function.Surjective (causalLowerRecovery t) ↔ t = 0 := by
  constructor
  · intro hs
    apply (causalLowerCauchyEvolution_injective_iff t).1
    intro u v huv
    obtain ⟨u',rfl⟩ := hs u
    obtain ⟨v',rfl⟩ := hs v
    have hleft (y : hardyL2ᗮ) : causalLowerCauchyEvolution t (causalLowerRecovery t y) = y := by
      have h := congrArg (fun T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ => T y)
        (causalLowerCauchyEvolution_comp_adjoint t)
      rw [causalLowerCauchyEvolution_adjoint] at h
      exact h
    rw [hleft,hleft] at huv
    exact congrArg (causalLowerRecovery t) huv
  · rintro rfl
    intro u
    refine ⟨u,?_⟩
    apply Subtype.ext
    change evolution (-0) u.val = u.val
    simp only [neg_zero,evolution_zero]

end
end RHTower.FokasLenells
