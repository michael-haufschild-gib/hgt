import GaloisForLFunctions.HTGeometry.CenteredGenericGalois

/-!
# The symmetric group acts on the centered roots by its own permutation

The automorphism attached to a permutation acts on the centered roots by that permutation, because
the action on the ambient field permutes the roots by construction.

So the Galois action on the roots of the centered polynomial is surjective onto the permutations,
which is what the discriminant argument and the base change step ask of it.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- **The automorphism attached to a permutation moves the roots by that permutation.** -/
theorem centeredPermAlgEquiv_centeredRootIn (e : Equiv.Perm (Fin d)) (i : Fin d) :
    centeredPermAlgEquiv K d e (centeredRootIn K d i) = centeredRootIn K d (e i) := by
  refine Subtype.ext ?_
  show ((e • centeredRootIn K d i : centeredField K d) : SymmetricRationalField K d) =
    centeredRoot K d (e i)
  rw [coe_smul_centeredField]
  exact smul_centeredRoot e i

/-- **The Galois action on the centered roots is surjective.** -/
theorem exists_centeredAut_perm (e : Equiv.Perm (Fin d)) :
    ∃ σ : (centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d),
      ∀ i, σ (centeredRootIn K d i) = centeredRootIn K d (e i) :=
  ⟨centeredPermAlgEquiv K d e, centeredPermAlgEquiv_centeredRootIn e⟩

end GaloisForLFunctions.HTGeometry
