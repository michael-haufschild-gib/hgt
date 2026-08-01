import GaloisForLFunctions.HTGeometry.CenteredRadicalBaseChange
import GaloisForLFunctions.HTGeometry.CenteredCoeffFieldRational
import GaloisForLFunctions.HTGeometry.RadicalRootFieldDegree

/-!
# Full symmetric monodromy of the centered equation survives an odd radical base change

At an odd exponent no square-class computation is needed: the radical extension has odd degree, so
it cannot contain the quadratic subextension cut out by the discriminant.

What the step still needs is that a root of the radical polynomial has full degree, and that is the
rational function model of the coefficient field — the constant coefficient is one of its variables,
hence prime, so the radical polynomial is irreducible.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

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
      Equiv.Perm (Fin d) := by
  haveI : CharZero (centeredCoeffField K d) :=
    charZero_of_injective_algebraMap (algebraMap K (centeredCoeffField K d)).injective
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hd0 : 0 < d := by omega
  have hd1 : 0 < d - 1 := by omega
  have hq : (Polynomial.X ^ n - Polynomial.C (centeredConstant K d hd0) :
      Polynomial (centeredCoeffField K d)) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C _ (by omega)).ne_zero
  have hsplitq := splits_of_splits_mul_right
    (L := (centeredMonicE K d *
      (Polynomial.X ^ n - Polynomial.C (centeredConstant K d hd0))).SplittingField)
    centeredMonicE_ne_zero hq
    (Polynomial.IsSplittingField.splits' (K := centeredCoeffField K d)
      (L := (centeredMonicE K d *
        (Polynomial.X ^ n - Polynomial.C (centeredConstant K d hd0))).SplittingField)
      (f := centeredMonicE K d *
        (Polynomial.X ^ n - Polynomial.C (centeredConstant K d hd0))))
  obtain ⟨α, -, hαpow⟩ := exists_pow_eq_mem_rootField hn hsplitq
  exact radicalBaseChangeOdd centeredMonicE_ne_zero hn
    (centeredGaloisEquiv K d).symm
    (primitiveRoots_nonempty_of_algebra K (centeredCoeffField K d) hn)
    hαpow
    (le_of_eq (finrank_adjoin_centeredConstant_root hd0 hd1 hn hαpow).symm)
    (not_two_dvd_finrank_rootField centeredMonicE_ne_zero hn
      (primitiveRoots_nonempty_of_algebra K (centeredCoeffField K d) hn)
      (irreducible_X_pow_sub_C_centeredConstant hd0 hd1 hn) hodd)

end GaloisForLFunctions.HTGeometry
