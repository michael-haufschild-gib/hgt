import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel
import GaloisForLFunctions.RepresentationLifting.Symplectic.PermutationOrbitDimensions

/-!
# Observation quotients of permutation constraint spaces

Linear observations modulo those factoring through the constraint equations
are exactly observations on the constrained sector. For permutation invariance
with a zero-sum constraint, each orbit beyond the first contributes one copy
of the observation space.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open scoped BigOperators
open OperatorKernels

variable {J W : Type*} {m : ℕ} [AddCommGroup W] [Module ℂ W]

/-- The complex-linear operator given by a family of real constraint rows. -/
def realConstraintOperator (A : Matrix J (Fin m) ℝ) : (Fin m → ℂ) →ₗ[ℂ] (J → ℂ) where
  toFun v j := ∑ i, (A j i : ℂ) * v i
  map_add' v w := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem realConstraintOperator_kernel (A : Matrix J (Fin m) ℝ) :
    (realConstraintOperator A).ker = realConstraintKernel A := by
  ext v
  exact funext_iff

/-- The obstruction depends on the actual constrained sector, not the number of equations. -/
theorem realConstraint_observation_defect [FiniteDimensional ℂ W]
    (A : Matrix J (Fin m) ℝ) :
    Module.finrank ℂ (((Fin m → ℂ) →ₗ[ℂ] W) ⧸
      (precompose (W := W) (realConstraintOperator A)).range) =
      Module.finrank ℂ W * Module.finrank ℂ (realConstraintKernel A) := by
  rw [finrank_compositionCokernel, realConstraintOperator_kernel]

/-- Arbitrary permutation families have an exact orbit-count obstruction. -/
theorem permutationMoving_observation_defect [FiniteDimensional ℂ W]
    {κ : Type*} (σ : κ → Equiv.Perm (Fin m)) :
    Module.finrank ℂ (((Fin m → ℂ) →ₗ[ℂ] W) ⧸
      (precompose (W := W) (realConstraintOperator (permutationMovingConstraints σ))).range) =
      Module.finrank ℂ W * (Nat.card (Quotient (permutationOrbit σ)) - 1) := by
  rw [realConstraint_observation_defect, permutationMoving_finrank]

/-- With vector-valued output, every free orbit constant contributes the ambient dimension. -/
theorem permutationMoving_endomorphism_defect
    {κ : Type*} (σ : κ → Equiv.Perm (Fin m)) :
    Module.finrank ℂ (Module.End ℂ (Fin m → ℂ) ⧸
      (precompose (W := Fin m → ℂ)
        (realConstraintOperator (permutationMovingConstraints σ))).range) =
      m * (Nat.card (Quotient (permutationOrbit σ)) - 1) := by
  rw [permutationMoving_observation_defect]
  simp

/-- Transitivity makes every linear observation factor through the real constraint rows. -/
theorem transitiveAction_observation_factors {A : Type*} [AddCommGroup A] (n : ℕ)
    (ρ : TransitiveActions.Transitive A (Fin (n + 1)) 0)
    (f : (Fin (n + 1) → ℂ) →ₗ[ℂ] W) :
    ∃ g, g.comp (realConstraintOperator
      (permutationMovingConstraints (fun a => (ρ.val a).toMul))) = f := by
  let T := realConstraintOperator (permutationMovingConstraints (fun a => (ρ.val a).toMul))
  have hk : T.ker = ⊥ := by
    rw [T, realConstraintOperator_kernel, transitiveAction_movingKernel_eq_bot]
  change f ∈ (precompose T).range
  rw [range_precompose]
  apply LinearMap.ext
  intro v
  have hv : v.val = 0 := by
    have := v.property
    rw [hk] at this
    exact this
  change f v.val = 0
  rw [hv, map_zero]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.permutationMoving_observation_defect
#print axioms GaloisForLFunctions.RepresentationLifting.transitiveAction_observation_factors
