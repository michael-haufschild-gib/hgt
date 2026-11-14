import GaloisForLFunctions.RepresentationLifting.PermutationResolvent
import GaloisForLFunctions.HeckeKreinToeplitz.Index.LocallyPeriodicProjection
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The fixed-space projection at a cyclic resolvent pole

At scalar `1`, the finite resolvent numerator is the cyclic orbit sum.
Dividing by the permutation order gives the canonical projection onto fixed
vectors, with kernel the moving subspace. This identifies the matrix
factorization with the existing algebraic periodic-orbit decomposition.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open GaloisForLFunctions.HeckeKreinToeplitz

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]

/-- The permutation action on coefficient vectors. -/
def permutationVectorAction (σ : Equiv.Perm ι) : Module.End K (ι → K) :=
  Matrix.toLinAlgEquiv' (σ.permMatrix K)

omit [CharZero K] in
theorem permutationVectorAction_periodic (σ : Equiv.Perm ι) (v : ι → K) :
    ∃ m : ℕ, m ≠ 0 ∧ (permutationVectorAction σ ^ m) v = v := by
  refine ⟨orderOf σ, Nat.ne_of_gt (orderOf_pos σ), ?_⟩
  unfold permutationVectorAction
  rw [← map_pow, permutationMatrix_period, map_one]
  rfl

/-- Canonical projection onto the fixed vectors of a permutation. -/
def permutationFixedProjection (σ : Equiv.Perm ι) : Module.End K (ι → K) :=
  locallyPeriodicProjection (permutationVectorAction σ) (permutationVectorAction_periodic σ)

/-- The normalized value of the finite numerator at `1` is the fixed-space projection. -/
theorem permutationFixedProjection_eq_numerator (σ : Equiv.Perm ι) :
    permutationFixedProjection (K := K) σ =
      (orderOf σ : K)⁻¹ • Matrix.toLinAlgEquiv' (permutationNumerator σ (1 : K)) := by
  apply LinearMap.ext
  intro v
  have hp : (permutationVectorAction (K := K) σ ^ orderOf σ) v = v := by
    unfold permutationVectorAction
    rw [← map_pow, permutationMatrix_period, map_one]
    rfl
  rw [permutationFixedProjection, locallyPeriodicProjection_eq_average _ _
    (Nat.ne_of_gt (orderOf_pos σ)) hp]
  simp only [periodicOrbitAverage, permutationNumerator, one_pow, one_smul,
    map_sum, map_pow, permutationVectorAction]

theorem permutationFixedProjection_fixed (σ : Equiv.Perm ι) (v : ι → K) :
    permutationVectorAction σ (permutationFixedProjection σ v) = permutationFixedProjection σ v :=
  locallyPeriodicProjection_fixed _ _ _

/-- The fixed projection is idempotent without a separate periodicity premise. -/
theorem permutationFixedProjection_idempotent (σ : Equiv.Perm ι) :
    permutationFixedProjection (K := K) σ * permutationFixedProjection σ =
      permutationFixedProjection σ := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply]
  unfold permutationFixedProjection
  apply locallyPeriodicProjection_apply_of_fixed
  exact locallyPeriodicProjection_fixed _ _ _

/-- Its image is exactly the fixed-vector subspace. -/
theorem permutationFixedProjection_range (σ : Equiv.Perm ι) :
    LinearMap.range (permutationFixedProjection (K := K) σ) =
      LinearMap.ker (permutationVectorAction σ - 1) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change permutationVectorAction σ (permutationFixedProjection σ w) -
      permutationFixedProjection σ w = 0
    rw [permutationFixedProjection_fixed, sub_self]
  · intro h
    have hv : permutationVectorAction σ v = v := sub_eq_zero.mp h
    exact ⟨v, locallyPeriodicProjection_apply_of_fixed _ _ hv⟩

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.permutationFixedProjection_eq_numerator
#print axioms GaloisForLFunctions.RepresentationLifting.permutationFixedProjection_range
