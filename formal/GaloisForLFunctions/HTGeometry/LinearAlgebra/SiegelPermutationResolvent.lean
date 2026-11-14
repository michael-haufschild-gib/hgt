import GaloisForLFunctions.HTGeometry.SiegelOrbit
import GaloisForLFunctions.RepresentationLifting.PermutationResolvent

/-!
# Cyclic denominator clearing for integral lattice permutations

The integral and real permutation matrices used by Siegel reduction have the
same finite geometric resolvent numerator. The identities hold before
localization, including at singular scalar values.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RepresentationLifting
open scoped BigOperators

variable {n : ℕ}

theorem permMatrixInt_eq_permMatrix (σ : Equiv.Perm (Fin n)) :
    permMatrixInt σ = σ.permMatrix ℤ := by
  ext i j
  simp [permMatrixInt, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

theorem siegelPermMatrix_eq_permMatrix (σ : Equiv.Perm (Fin n)) :
    permMatrix σ = σ.permMatrix ℝ := by
  ext i j
  simp [permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

/-- The cyclic resolvent identity already holds over the integral coefficient ring. -/
theorem permMatrixInt_resolvent_factorization (σ : Equiv.Perm (Fin n)) (s : ℤ) :
    (1 - s • permMatrixInt σ) *
        (∑ k ∈ Finset.range (orderOf σ), s ^ k • (permMatrixInt σ) ^ k) =
      (1 - s ^ orderOf σ) • 1 ∧
    (∑ k ∈ Finset.range (orderOf σ), s ^ k • (permMatrixInt σ) ^ k) *
        (1 - s • permMatrixInt σ) = (1 - s ^ orderOf σ) • 1 := by
  simpa only [permMatrixInt_eq_permMatrix, permutationNumerator] using
    permutationNumerator_factorization σ s

/-- The same numerator clears the real lattice-basis permutation resolvent. -/
theorem siegelPermMatrix_resolvent_factorization (σ : Equiv.Perm (Fin n)) (s : ℝ) :
    (1 - s • permMatrix σ) *
        (∑ k ∈ Finset.range (orderOf σ), s ^ k • (permMatrix σ) ^ k) =
      (1 - s ^ orderOf σ) • 1 ∧
    (∑ k ∈ Finset.range (orderOf σ), s ^ k • (permMatrix σ) ^ k) *
        (1 - s • permMatrix σ) = (1 - s ^ orderOf σ) • 1 := by
  simpa only [siegelPermMatrix_eq_permMatrix, permutationNumerator] using
    permutationNumerator_factorization σ s

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.permMatrixInt_resolvent_factorization
#print axioms GaloisForLFunctions.HTGeometry.siegelPermMatrix_resolvent_factorization
