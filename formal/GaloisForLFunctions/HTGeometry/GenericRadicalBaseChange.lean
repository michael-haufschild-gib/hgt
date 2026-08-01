import GaloisForLFunctions.HTGeometry.RadicalBaseChangeFromModel
import GaloisForLFunctions.HTGeometry.GenericPermRootAction
import GaloisForLFunctions.HTGeometry.SymmetricPartRadical
import GaloisForLFunctions.HTGeometry.CenteredGenericPolynomial

/-!
# The generic polynomial keeps its symmetric group after an even radical base change

Every input of the base change step is available for the generic polynomial over the symmetric part:
its Galois group there is the symmetric group, its roots are the generic roots, the action on them
is surjective, the symmetric part contains the roots of unity, and the radical polynomial over an
elementary symmetric function is irreducible, so a root of it has full degree.

What is left to the caller is the square class of the product of the two radicands.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}

/-- **The base change theorem for the generic polynomial.** -/
noncomputable def genericRadicalBaseChange (hd : 2 ≤ d) (i : Fin d) {m : ℕ} (hm : 0 < m)
    (hclass : ∀ e : symmetricPart K d,
      algebraMap (symmetricPart K d) (SymmetricRationalField K d) e =
        vandermondeProd (genericRoot K d) * vandermondeProd (genericRoot K d) →
      ¬ ∃ t : symmetricPart K d, e * esymmCoeffPart K d i = t * t) :
    ((genericMonic K d *
        (Polynomial.X ^ (2 * m) - Polynomial.C (esymmCoeffPart K d i))).SplittingField ≃ₐ[
        rootField (symmetricPart K d)
          (L := (genericMonic K d *
            (Polynomial.X ^ (2 * m) - Polynomial.C (esymmCoeffPart K d i))).SplittingField)
          (Polynomial.X ^ (2 * m) - Polynomial.C (esymmCoeffPart K d i))]
      (genericMonic K d *
        (Polynomial.X ^ (2 * m) - Polynomial.C (esymmCoeffPart K d i))).SplittingField) ≃*
      Equiv.Perm (Fin d) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  exact radicalBaseChangeEvenFromModel genericMonic_ne_zero hm
    (symmetricGaloisEquiv K d).symm
    (primitiveRoots_nonempty_symmetricPart K d (by omega))
    hd (genericRoot K d) genericRoot_injective
    (fun x => by
      rw [rootSet_genericMonic]
      exact ⟨fun ⟨j, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j, hj⟩⟩)
    exists_genericAut_perm
    (fun α hα => le_of_eq
      (finrank_adjoin_of_irreducible (by omega)
        (irreducible_X_pow_sub_C_esymmCoeffPart i (by omega)) hα).symm)
    hclass

end GaloisForLFunctions.HTGeometry
