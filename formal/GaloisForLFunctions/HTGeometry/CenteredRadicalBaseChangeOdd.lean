import GaloisForLFunctions.HTGeometry.CenteredRadicalBaseChange
import GaloisForLFunctions.HTGeometry.RadicalBaseChangeOddFromDegree

/-!
# The odd base change step for the centered generic polynomial

At an odd exponent the base change needs no square-class computation: the radical extension has odd
degree, so it cannot contain the quadratic subextension cut out by the discriminant.

What is left to the caller is the irreducibility of the radical polynomial and the degree of a root
of it.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option synthInstance.maxHeartbeats 400000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}

/-- **The odd base change theorem for the centered generic polynomial.** -/
noncomputable def centeredRadicalBaseChangeOdd (hd : 2 ≤ d)
    {c : centeredCoeffField K d} {n : ℕ} (hn : 0 < n)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c :
      Polynomial (centeredCoeffField K d)))
    (hodd : ¬ 2 ∣ n)
    (hdeg : ∀ α : (centeredMonicE K d *
        (Polynomial.X ^ n - Polynomial.C c)).SplittingField,
      α ^ n = algebraMap (centeredCoeffField K d) _ c →
      n ≤ Module.finrank (centeredCoeffField K d)
        (IntermediateField.adjoin (centeredCoeffField K d) {α})) :
    ((centeredMonicE K d * (Polynomial.X ^ n - Polynomial.C c)).SplittingField ≃ₐ[
        rootField (centeredCoeffField K d)
          (L := (centeredMonicE K d *
            (Polynomial.X ^ n - Polynomial.C c)).SplittingField)
          (Polynomial.X ^ n - Polynomial.C c)]
      (centeredMonicE K d * (Polynomial.X ^ n - Polynomial.C c)).SplittingField) ≃*
      Equiv.Perm (Fin d) := by
  haveI : CharZero (centeredCoeffField K d) :=
    charZero_of_injective_algebraMap (algebraMap K (centeredCoeffField K d)).injective
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  exact radicalBaseChangeOddFromDegree centeredMonicE_ne_zero hn
    (centeredGaloisEquiv K d).symm
    (primitiveRoots_nonempty_of_algebra K (centeredCoeffField K d) hn)
    hirr hodd hdeg

end GaloisForLFunctions.HTGeometry
