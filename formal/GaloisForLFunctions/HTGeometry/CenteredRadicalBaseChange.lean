import GaloisForLFunctions.HTGeometry.RadicalBaseChangeFromModel
import GaloisForLFunctions.HTGeometry.CenteredPermRootAction
import GaloisForLFunctions.HTGeometry.CenteredSplittingField
import GaloisForLFunctions.HTGeometry.PrimitiveRootTransport

/-!
# The centered generic polynomial keeps its symmetric group after an even radical base change

All the data the base change step needs is available for the centered generic polynomial: its
Galois group over its coefficient field is the symmetric group, its roots are enumerated by the
centered roots, the action on them is surjective, and the constants contain the roots of unity.

What is left to the caller is the degree of the radical generator and the square class of the
product of the two radicands — the two facts that are specific to the equation at hand.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}

/-- **The base change theorem for the centered generic polynomial.** -/
noncomputable def centeredRadicalBaseChange (hd : 2 ≤ d)
    {c : centeredCoeffField K d} {m : ℕ} (hm : 0 < m)
    (hdeg : ∀ α : (centeredMonicE K d *
        (Polynomial.X ^ (2 * m) - Polynomial.C c)).SplittingField,
      α ^ (2 * m) = algebraMap (centeredCoeffField K d) _ c →
      2 * m ≤ Module.finrank (centeredCoeffField K d)
        (IntermediateField.adjoin (centeredCoeffField K d) {α}))
    (hclass : ∀ e : centeredCoeffField K d,
      algebraMap (centeredCoeffField K d) (centeredField K d) e =
        vandermondeProd (centeredRootIn K d) * vandermondeProd (centeredRootIn K d) →
      ¬ ∃ t : centeredCoeffField K d, e * c = t * t) :
    ((centeredMonicE K d * (Polynomial.X ^ (2 * m) - Polynomial.C c)).SplittingField ≃ₐ[
        rootField (centeredCoeffField K d)
          (L := (centeredMonicE K d *
            (Polynomial.X ^ (2 * m) - Polynomial.C c)).SplittingField)
          (Polynomial.X ^ (2 * m) - Polynomial.C c)]
      (centeredMonicE K d * (Polynomial.X ^ (2 * m) - Polynomial.C c)).SplittingField) ≃*
      Equiv.Perm (Fin d) := by
  haveI : CharZero (centeredCoeffField K d) :=
    charZero_of_injective_algebraMap (algebraMap K (centeredCoeffField K d)).injective
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  exact radicalBaseChangeEvenFromModel centeredMonicE_ne_zero hm
    (centeredGaloisEquiv K d).symm
    (primitiveRoots_nonempty_of_algebra K (centeredCoeffField K d) (by omega))
    hd (centeredRootIn K d) centeredRootIn_injective
    (fun x => by
      rw [rootSet_centeredMonicE]
      exact ⟨fun ⟨i, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, hi⟩⟩)
    exists_centeredAut_perm hdeg hclass

end GaloisForLFunctions.HTGeometry
