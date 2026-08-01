import GaloisForLFunctions.HTGeometry.GenericRadicalBaseChange
import GaloisForLFunctions.HTGeometry.RadicalBaseChangeOddFromDegree

/-!
# Full symmetric monodromy survives an odd radical base change

At an odd exponent the radical extension has odd degree, so it cannot contain the quadratic
subextension cut out by the discriminant and no square-class computation is needed.

The radical polynomial over an elementary symmetric function is irreducible at every exponent, so a
root of it has full degree, and nothing else is left: the Galois group of the generic polynomial over
its coefficient field remains the full symmetric group after adjoining an odd radical of one of its
coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}

/-- **Full symmetric monodromy survives an odd radical base change.** -/
noncomputable def genericFullMonodromyOdd (hd : 2 ≤ d) (i : Fin d) {n : ℕ} (hn : 0 < n)
    (hodd : ¬ 2 ∣ n) :
    ((genericMonic K d *
        (Polynomial.X ^ n -
          Polynomial.C (esymmCoeffPart K d i))).SplittingField ≃ₐ[
        rootField (symmetricPart K d)
          (L := (genericMonic K d *
            (Polynomial.X ^ n -
              Polynomial.C (esymmCoeffPart K d i))).SplittingField)
          (Polynomial.X ^ n - Polynomial.C (esymmCoeffPart K d i))]
      (genericMonic K d *
        (Polynomial.X ^ n -
          Polynomial.C (esymmCoeffPart K d i))).SplittingField) ≃*
      Equiv.Perm (Fin d) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  have hirr := irreducible_X_pow_sub_C_esymmCoeffPart (K := K) (d := d) i hn
  exact radicalBaseChangeOddFromDegree genericMonic_ne_zero hn
    (symmetricGaloisEquiv K d).symm
    (primitiveRoots_nonempty_symmetricPart K d hn) hirr hodd
    (fun _ hα => le_of_eq (finrank_adjoin_of_irreducible hn hirr hα).symm)

end GaloisForLFunctions.HTGeometry
