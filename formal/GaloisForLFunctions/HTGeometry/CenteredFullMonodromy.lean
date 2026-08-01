import GaloisForLFunctions.HTGeometry.CenteredRadicalBaseChange
import GaloisForLFunctions.HTGeometry.CenteredSquareClassInput
import GaloisForLFunctions.HTGeometry.CenteredCoeffFieldRational

/-!
# Full symmetric monodromy of the centered equation survives the even radical base change

For the centered generic polynomial the base change step needs two inputs: a root of the radical
polynomial over the constant coefficient has full degree, and the discriminant times that constant
coefficient is not a square in the coefficient field.

The first is the rational function model of the coefficient field — the constant coefficient is one
of its variables, hence prime — and the second is the square-class computation.  Neither leaves a
hypothesis behind, so the Galois group of the centered equation over its coefficient field remains
the full symmetric group after adjoining an even radical of its constant coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}

/-- **Full symmetric monodromy of the centered equation survives the even radical base change.** -/
noncomputable def centeredFullMonodromy (hd : 3 ≤ d) {m : ℕ} (hm : 0 < m) :
    ((centeredMonicE K d *
        (Polynomial.X ^ (2 * m) -
          Polynomial.C (centeredConstant K d (by omega)))).SplittingField ≃ₐ[
        rootField (centeredCoeffField K d)
          (L := (centeredMonicE K d *
            (Polynomial.X ^ (2 * m) -
              Polynomial.C (centeredConstant K d (by omega)))).SplittingField)
          (Polynomial.X ^ (2 * m) -
            Polynomial.C (centeredConstant K d (by omega)))]
      (centeredMonicE K d *
        (Polynomial.X ^ (2 * m) -
          Polynomial.C (centeredConstant K d (by omega)))).SplittingField) ≃*
      Equiv.Perm (Fin d) :=
  centeredRadicalBaseChange (by omega) hm
    (fun _ hα => le_of_eq
      (finrank_adjoin_centeredConstant_root (by omega) (by omega) (by omega) hα).symm)
    (no_sqrt_centered_disc_mul_constant hd)

end GaloisForLFunctions.HTGeometry
