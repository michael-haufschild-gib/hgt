import GaloisForLFunctions.HTGeometry.BorelWeil.WeylAction
import GaloisForLFunctions.RepresentationLifting.PermutationResolvent

/-!
# Finite cyclic resolvents of Weyl permutation matrices

The Weyl matrices act on the left, opposite to mathlib's row-permutation
convention. Identifying the inverse permutation transfers the cyclic
resolvent factorization to the existing flag-coordinate action.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open GaloisForLFunctions.RepresentationLifting
open scoped BigOperators

variable {N : ℕ} {k : Type*} [Field k]

theorem permMat_eq_inverse_permMatrix (w : Equiv.Perm (Fin N)) :
    permMat w k = (w⁻¹).permMatrix k := by
  ext i j
  simp only [permMat, permWitness, Matrix.of_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff]
  congr 1
  apply propext
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have h' := congrArg w h
    simpa using h'

/-- A finite polynomial numerator clears the Weyl resolvent on both sides. -/
theorem weylMatrix_resolvent_factorization (w : Equiv.Perm (Fin N)) (s : k) :
    (1 - s • permMat w k) *
        (∑ j ∈ Finset.range (orderOf w), s ^ j • (permMat w k) ^ j) =
      (1 - s ^ orderOf w) • 1 ∧
    (∑ j ∈ Finset.range (orderOf w), s ^ j • (permMat w k) ^ j) *
        (1 - s • permMat w k) = (1 - s ^ orderOf w) • 1 := by
  simpa only [permMat_eq_inverse_permMatrix, permutationNumerator, orderOf_inv] using
    permutationNumerator_factorization (w⁻¹) s

end GaloisForLFunctions.HTGeometry.BorelWeil

#print axioms GaloisForLFunctions.HTGeometry.BorelWeil.weylMatrix_resolvent_factorization
