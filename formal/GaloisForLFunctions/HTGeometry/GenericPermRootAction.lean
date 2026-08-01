import GaloisForLFunctions.HTGeometry.GenericRootSet

/-!
# The symmetric group acts on the generic roots by its own permutation

The automorphism attached to a permutation acts on the generic roots by that permutation, since the
action on the rational function field permutes the variables.

So the Galois action on the roots of the generic polynomial is surjective onto the permutations,
which is what the discriminant argument and the base change step ask of it.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {d : ℕ}

/-- **The Galois action on the generic roots is surjective.** -/
theorem exists_genericAut_perm (e : Equiv.Perm (Fin d)) :
    ∃ σ : SymmetricRationalField K d ≃ₐ[symmetricPart K d] SymmetricRationalField K d,
      ∀ i, σ (genericRoot K d i) = genericRoot K d (e i) :=
  ⟨symmetricGaloisEquiv K d e, fun i => by
    rw [symmetricGaloisEquiv_apply]
    exact smul_genericRoot e i⟩

end GaloisForLFunctions.HTGeometry
