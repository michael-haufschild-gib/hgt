import GaloisForLFunctions.HTGeometry.FiniteReplicaCollectiveCommutantExact
import GaloisForLFunctions.RepresentationLifting.PermutationResolvent
import GaloisForLFunctions.RepresentationLifting.PermutationProjection

/-!
# Cyclic resolvents in the replica collective commutant

A permutation of replica positions permutes the configuration basis. The cyclic
geometric numerator therefore clears its resolvent denominator, and every term
continues to commute with the collective physical matrix units.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RepresentationLifting

/-- The induced permutation of the tensor configuration basis. -/
def replicaConfigurationPerm (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin r → Fin d) where
  toFun x q := x (σ.symm q)
  invFun x q := x (σ q)
  left_inv x := by funext q; simp
  right_inv x := by funext q; simp

theorem replicaPermutationMatrix_eq_permMatrix (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    replicaPermutationMatrix r d σ = (replicaConfigurationPerm r d σ).permMatrix ℂ := by
  ext x y
  simp only [replicaPermutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_some_iff]
  congr 1
  apply propext
  constructor
  · intro h
    funext q
    simpa [replicaConfigurationPerm] using congrFun h (σ.symm q)
  · intro h
    funext q
    simpa [replicaConfigurationPerm] using congrFun h (σ q)

/-- Finite numerator, with period measured on the actual configuration space. -/
def replicaResolventNumerator (r d : ℕ) (σ : Equiv.Perm (Fin r)) (s : ℂ) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ :=
  permutationNumerator (replicaConfigurationPerm r d σ) s

theorem replicaResolventNumerator_factorization
    (r d : ℕ) (σ : Equiv.Perm (Fin r)) (s : ℂ) :
    (1 - s • replicaPermutationMatrix r d σ) * replicaResolventNumerator r d σ s =
        (1 - s ^ orderOf (replicaConfigurationPerm r d σ)) • 1 ∧
      replicaResolventNumerator r d σ s * (1 - s • replicaPermutationMatrix r d σ) =
        (1 - s ^ orderOf (replicaConfigurationPerm r d σ)) • 1 := by
  rw [replicaPermutationMatrix_eq_permMatrix]
  exact permutationNumerator_factorization _ _

/-- Clearing a cyclic denominator preserves all collective symmetries. -/
theorem replicaResolventNumerator_mem_collectiveCommutant
    (r d : ℕ) (σ : Equiv.Perm (Fin r)) (s : ℂ) :
    replicaResolventNumerator r d σ s ∈ finiteReplicaCollectiveCommutant r d := by
  unfold replicaResolventNumerator permutationNumerator
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  rw [← replicaPermutationMatrix_eq_permMatrix]
  intro b a
  exact (Commute.pow_right
    (replicaPermutationMatrix_mem_collectiveCommutant r d σ b a) k).eq

/-- Projection onto tensors fixed by the selected replica permutation. -/
def replicaCyclicProjection (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    Module.End ℂ ((Fin r → Fin d) → ℂ) :=
  permutationFixedProjection (replicaConfigurationPerm r d σ)

theorem replicaCyclicProjection_eq_numerator (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    replicaCyclicProjection r d σ =
      (orderOf (replicaConfigurationPerm r d σ) : ℂ)⁻¹ •
        Matrix.toLinAlgEquiv' (replicaResolventNumerator r d σ 1) :=
  permutationFixedProjection_eq_numerator _

theorem replicaCyclicProjection_idempotent (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    replicaCyclicProjection r d σ * replicaCyclicProjection r d σ =
      replicaCyclicProjection r d σ :=
  permutationFixedProjection_idempotent _

/-- The projection image is the literal fixed-tensor kernel in replica coordinates. -/
theorem replicaCyclicProjection_range (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    LinearMap.range (replicaCyclicProjection r d σ) =
      LinearMap.ker ((replicaPermutationMatrix r d σ).mulVecLin - 1) := by
  have haction : permutationVectorAction (replicaConfigurationPerm r d σ) =
      (replicaPermutationMatrix r d σ).mulVecLin := by
    rw [replicaPermutationMatrix_eq_permMatrix]
    apply LinearMap.ext
    intro v
    exact Matrix.toLinAlgEquiv'_apply _ v
  rw [replicaCyclicProjection, permutationFixedProjection_range, haction]

/-- The normalized projector preserves every collective physical symmetry. -/
theorem replicaCyclicProjectionMatrix_mem_collectiveCommutant
    (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    (orderOf (replicaConfigurationPerm r d σ) : ℂ)⁻¹ • replicaResolventNumerator r d σ 1 ∈
      finiteReplicaCollectiveCommutant r d :=
  Submodule.smul_mem _ _ (replicaResolventNumerator_mem_collectiveCommutant r d σ 1)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.replicaResolventNumerator_factorization
#print axioms GaloisForLFunctions.HTGeometry.replicaResolventNumerator_mem_collectiveCommutant
#print axioms GaloisForLFunctions.HTGeometry.replicaCyclicProjection_range
