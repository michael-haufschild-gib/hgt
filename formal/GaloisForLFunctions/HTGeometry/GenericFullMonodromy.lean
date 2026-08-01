import GaloisForLFunctions.HTGeometry.GenericRadicalBaseChange
import GaloisForLFunctions.HTGeometry.GenericSquareClassInput

/-!
# Full symmetric monodromy survives the even radical base change

Combining the base change theorem for the generic polynomial with the square-class computation for
its discriminant and its constant coefficient leaves no hypotheses beyond the degree being at least
three and the exponent being even and positive.

So the Galois group of the generic polynomial over its coefficient field remains the full symmetric
group after adjoining an even radical of the constant coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}

/-- **Full symmetric monodromy survives the even radical base change.** -/
noncomputable def genericFullMonodromy (hd : 3 ≤ d) {m : ℕ} (hm : 0 < m) :
    ((genericMonic K d *
        (Polynomial.X ^ (2 * m) -
          Polynomial.C (esymmCoeffPart K d (topIndex d (by omega))))).SplittingField ≃ₐ[
        rootField (symmetricPart K d)
          (L := (genericMonic K d *
            (Polynomial.X ^ (2 * m) -
              Polynomial.C (esymmCoeffPart K d (topIndex d (by omega))))).SplittingField)
          (Polynomial.X ^ (2 * m) -
            Polynomial.C (esymmCoeffPart K d (topIndex d (by omega))))]
      (genericMonic K d *
        (Polynomial.X ^ (2 * m) -
          Polynomial.C (esymmCoeffPart K d (topIndex d (by omega))))).SplittingField) ≃*
      Equiv.Perm (Fin d) :=
  genericRadicalBaseChange (by omega) (topIndex d (by omega)) hm
    (no_sqrt_generic_disc_mul_esymm (by omega) _ (coe_esymmCoeffPart _))

end GaloisForLFunctions.HTGeometry
