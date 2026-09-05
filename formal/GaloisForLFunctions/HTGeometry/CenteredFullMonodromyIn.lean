import GaloisForLFunctions.HTGeometry.CenteredRadicalBaseChangeIn
import GaloisForLFunctions.HTGeometry.CenteredCoeffFieldRational
import GaloisForLFunctions.HTGeometry.CenteredSquareClassInput

/-!
# Full symmetric monodromy of the centered equation, in any ambient splitting field

Both inputs of the base change step are statements about the coefficient field alone: the radical
polynomial over the constant coefficient is irreducible because that coefficient is a variable of a
rational function field, and the discriminant times it is not a square.

So the conclusion holds in any ambient splitting field of the centered polynomial together with the
radical, at every exponent, with no hypothesis beyond the degree.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option synthInstance.maxHeartbeats 800000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}
variable {L : Type*} [Field L] [Algebra (centeredCoeffField K d) L]

/-- **Full symmetric monodromy at an even exponent, in any ambient.** -/
noncomputable def centeredFullMonodromyIn (hd : 3 ≤ d) {m : ℕ} (hm : 0 < m)
    [Polynomial.IsSplittingField (centeredCoeffField K d) L
      (centeredMonicE K d *
        (Polynomial.X ^ (2 * m) -
          Polynomial.C (centeredConstant K d (by omega))))] :
    (L ≃ₐ[rootField (centeredCoeffField K d) (L := L)
        (Polynomial.X ^ (2 * m) -
          Polynomial.C (centeredConstant K d (by omega)))] L) ≃* Equiv.Perm (Fin d) :=
  centeredRadicalBaseChangeIn (by omega) hm
    (fun _ hα => le_of_eq
      (finrank_adjoin_centeredConstant_root (by omega) (by omega) (by omega) hα).symm)
    (no_sqrt_centered_disc_mul_constant hd)

/-- **Full symmetric monodromy at an odd exponent, in any ambient.** -/
noncomputable def centeredFullMonodromyOddIn (hd : 3 ≤ d) {n : ℕ} (hn : 0 < n)
    (hodd : ¬ 2 ∣ n)
    [Polynomial.IsSplittingField (centeredCoeffField K d) L
      (centeredMonicE K d *
        (Polynomial.X ^ n - Polynomial.C (centeredConstant K d (by omega))))] :
    (L ≃ₐ[rootField (centeredCoeffField K d) (L := L)
        (Polynomial.X ^ n -
          Polynomial.C (centeredConstant K d (by omega)))] L) ≃* Equiv.Perm (Fin d) :=
  centeredRadicalBaseChangeOddIn (by omega) hn
    (irreducible_X_pow_sub_C_centeredConstant (by omega) (by omega) hn) hodd
    (fun _ hα => le_of_eq
      (finrank_adjoin_centeredConstant_root (by omega) (by omega) hn hα).symm)

end GaloisForLFunctions.HTGeometry
