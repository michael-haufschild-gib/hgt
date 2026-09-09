import GaloisForLFunctions.RHTower.FokasLenellsCausalCoisometry

/-!
# Exact information loss and minimum-norm recovery

The actual coisometric Cauchy evolution splits every completed datum into
orthogonal recoverable and lost parts. Energy loss is exactly the squared
norm of its kernel component. Each output fibre is an affine translate of
the actual kernel, with the opposite-time adjoint as its unique minimum-norm
representative.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

private theorem forward_adjoint (t : ℝ≥0) (u : hardyL2ᗮ) :
    causalLowerCauchyEvolution t ((causalLowerCauchyEvolution t).adjoint u) = u :=
  congrArg (fun T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ => T u) (causalLowerCauchyEvolution_comp_adjoint t)

/-- The actual recoverable-data projection, obtained by forward evolution then adjoint recovery. -/
def causalRecoveryProjection (t : ℝ≥0) : hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  (causalLowerCauchyEvolution t).adjoint.comp (causalLowerCauchyEvolution t)

/-- The actual information-loss projection complementary to recoverable data. -/
def causalLossProjection (t : ℝ≥0) : hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  ContinuousLinearMap.id ℂ (hardyL2ᗮ) - causalRecoveryProjection t

/-- Adjoint recovery is an actual idempotent projection. -/
theorem causalRecoveryProjection_idempotent (t : ℝ≥0) (u : hardyL2ᗮ) :
    causalRecoveryProjection t (causalRecoveryProjection t u) = causalRecoveryProjection t u := by
  change (causalLowerCauchyEvolution t).adjoint
    (causalLowerCauchyEvolution t ((causalLowerCauchyEvolution t).adjoint (causalLowerCauchyEvolution t u))) = _
  rw [forward_adjoint]
  rfl

/-- The recoverable-data projection is self-adjoint in the original completed L² metric. -/
theorem causalRecoveryProjection_adjoint (t : ℝ≥0) :
    (causalRecoveryProjection t).adjoint = causalRecoveryProjection t := by
  simp only [causalRecoveryProjection,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

/-- The information-loss component is killed by the actual forward operator. -/
theorem causalLowerCauchyEvolution_loss_zero (t : ℝ≥0) (u : hardyL2ᗮ) :
    causalLowerCauchyEvolution t (causalLossProjection t u) = 0 := by
  change causalLowerCauchyEvolution t (u-(causalLowerCauchyEvolution t).adjoint (causalLowerCauchyEvolution t u)) = 0
  rw [map_sub,forward_adjoint,sub_self]

/-- Recoverable and lost components are exactly orthogonal. -/
theorem causalRecoveryProjection_inner_loss (t : ℝ≥0) (u : hardyL2ᗮ) :
    inner ℂ (causalRecoveryProjection t u) (causalLossProjection t u) = 0 := by
  change inner ℂ ((causalLowerCauchyEvolution t).adjoint (causalLowerCauchyEvolution t u))
    (causalLossProjection t u) = 0
  rw [ContinuousLinearMap.adjoint_inner_left,causalLowerCauchyEvolution_loss_zero,inner_zero_right]

/-- The completed datum splits exactly into retained output energy and lost kernel energy. -/
theorem causalLowerCauchyEvolution_energy_decomposition (t : ℝ≥0) (u : hardyL2ᗮ) :
    ‖u‖^2 = ‖causalLowerCauchyEvolution t u‖^2 + ‖causalLossProjection t u‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (causalRecoveryProjection t u) (causalLossProjection t u) (causalRecoveryProjection_inner_loss t u)
  have he : causalRecoveryProjection t u + causalLossProjection t u = u := by
    change causalRecoveryProjection t u + (u-causalRecoveryProjection t u) = u
    abel
  have hn : ‖causalRecoveryProjection t u‖ = ‖causalLowerCauchyEvolution t u‖ :=
    norm_causalLowerCauchyEvolution_adjoint_apply t (causalLowerCauchyEvolution t u)
  simpa only [he,hn,pow_two] using h

/-- Norm is preserved exactly for data with no component in the lost subspace. -/
theorem causalLowerCauchyEvolution_norm_eq_iff (t : ℝ≥0) (u : hardyL2ᗮ) :
    ‖causalLowerCauchyEvolution t u‖ = ‖u‖ ↔ causalLossProjection t u = 0 := by
  have he := causalLowerCauchyEvolution_energy_decomposition t u
  constructor
  · intro h
    rw [h] at he
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (causalLossProjection t u)]
  · intro h
    rw [h,norm_zero] at he
    nlinarith [norm_nonneg u,norm_nonneg (causalLowerCauchyEvolution t u)]

/-- Every actual output fibre is precisely an adjoint recovery plus an arbitrary actual kernel vector. -/
theorem causalLowerCauchyEvolution_fibre (t : ℝ≥0) (u y : hardyL2ᗮ) :
    causalLowerCauchyEvolution t u = y ↔
      ∃ k : (causalLowerCauchyEvolution t).ker,
        u = (causalLowerCauchyEvolution t).adjoint y + k.val := by
  constructor
  · intro h
    refine ⟨⟨u-(causalLowerCauchyEvolution t).adjoint y,?_⟩,?_⟩
    · change causalLowerCauchyEvolution t (u-(causalLowerCauchyEvolution t).adjoint y) = 0
      rw [map_sub,h,forward_adjoint,sub_self]
    · change u = (causalLowerCauchyEvolution t).adjoint y +
        (u-(causalLowerCauchyEvolution t).adjoint y)
      rw [← add_sub_assoc,add_sub_cancel_left]
  · rintro ⟨k,rfl⟩
    rw [map_add,forward_adjoint]
    have hk : causalLowerCauchyEvolution t k.val = 0 := k.property
    rw [hk,add_zero]

/-- The isometric adjoint is the unique preimage whose norm is no larger than its output norm. -/
theorem causalLowerCauchyEvolution_minimum_norm_fibre (t : ℝ≥0) (u y : hardyL2ᗮ) :
    (causalLowerCauchyEvolution t u = y ∧ ‖u‖ ≤ ‖y‖) ↔
      u = (causalLowerCauchyEvolution t).adjoint y := by
  constructor
  · rintro ⟨hu,hn⟩
    have he : ‖causalLowerCauchyEvolution t u‖ = ‖u‖ :=
      le_antisymm (causalLowerCauchyEvolution_norm_le t u) (by simpa only [hu] using hn)
    have hz := (causalLowerCauchyEvolution_norm_eq_iff t u).1 he
    change u-(causalLowerCauchyEvolution t).adjoint (causalLowerCauchyEvolution t u) = 0 at hz
    rw [hu] at hz
    exact sub_eq_zero.mp hz
  · rintro rfl
    exact ⟨forward_adjoint t y,(norm_causalLowerCauchyEvolution_adjoint_apply t y).le⟩

/-- Each concrete positive-time witness is entirely lost by the actual orthogonal loss projection. -/
theorem causalLossProjection_witness (a : ℝ) :
    causalLossProjection ⟨Real.exp a,(Real.exp_pos a).le⟩ (causalCauchyKernelWitness a) = causalCauchyKernelWitness a := by
  change causalCauchyKernelWitness a - (causalLowerCauchyEvolution ⟨Real.exp a,(Real.exp_pos a).le⟩).adjoint
    (causalLowerCauchyEvolution ⟨Real.exp a,(Real.exp_pos a).le⟩ (causalCauchyKernelWitness a)) = _
  rw [causalLowerCauchyEvolution_kills_witness,map_zero,sub_zero]

end
end RHTower.FokasLenells
