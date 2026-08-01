import GaloisForLFunctions.HTGeometry.CenteredRadicalBaseChangeOdd
import GaloisForLFunctions.HTGeometry.CenteredCoeffFieldRational

/-!
# Full symmetric monodromy of the centered equation survives an odd radical base change

The rational function model of the coefficient field makes the constant coefficient a variable,
hence prime, so the radical polynomial over it is irreducible and a root of it has full degree.
Those are the two inputs of the odd base change step, and it leaves no hypothesis behind.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option synthInstance.maxHeartbeats 400000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}

/-- **Full symmetric monodromy of the centered equation survives an odd radical base change.** -/
noncomputable def centeredFullMonodromyOdd (hd : 3 ≤ d) {n : ℕ} (hn : 0 < n) (hodd : ¬ 2 ∣ n) :
    ((centeredMonicE K d *
        (Polynomial.X ^ n -
          Polynomial.C (centeredConstant K d (by omega)))).SplittingField ≃ₐ[
        rootField (centeredCoeffField K d)
          (L := (centeredMonicE K d *
            (Polynomial.X ^ n -
              Polynomial.C (centeredConstant K d (by omega)))).SplittingField)
          (Polynomial.X ^ n -
            Polynomial.C (centeredConstant K d (by omega)))]
      (centeredMonicE K d *
        (Polynomial.X ^ n -
          Polynomial.C (centeredConstant K d (by omega)))).SplittingField) ≃*
      Equiv.Perm (Fin d) :=
  centeredRadicalBaseChangeOdd (by omega) hn
    (irreducible_X_pow_sub_C_centeredConstant (by omega) (by omega) hn) hodd
    (fun _ hα => le_of_eq
      (finrank_adjoin_centeredConstant_root (by omega) (by omega) hn hα).symm)

end GaloisForLFunctions.HTGeometry
