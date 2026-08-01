import GaloisForLFunctions.HTGeometry.CenteredRadicalBaseChange
import GaloisForLFunctions.HTGeometry.RadicalBaseChangeOddFromDegree

/-!
# The base change step for the centered polynomial in any ambient splitting field

The base change step needs only that the ambient field is a splitting field of the centered
polynomial together with the radical; which splitting field it is plays no role.

Stating it that way lets the conclusion be read in an ambient introduced by a later construction,
without ever comparing that ambient with the canonical splitting field.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}
variable {L : Type*} [Field L] [Algebra (centeredCoeffField K d) L]

/-- **The even base change theorem for the centered polynomial, in any ambient.** -/
noncomputable def centeredRadicalBaseChangeIn (hd : 2 ≤ d)
    {c : centeredCoeffField K d} {m : ℕ} (hm : 0 < m)
    [Polynomial.IsSplittingField (centeredCoeffField K d) L
      (centeredMonicE K d * (Polynomial.X ^ (2 * m) - Polynomial.C c))]
    (hdeg : ∀ α : L, α ^ (2 * m) = algebraMap (centeredCoeffField K d) L c →
      2 * m ≤ Module.finrank (centeredCoeffField K d)
        (IntermediateField.adjoin (centeredCoeffField K d) {α}))
    (hclass : ∀ e : centeredCoeffField K d,
      algebraMap (centeredCoeffField K d) (centeredField K d) e =
        vandermondeProd (centeredRootIn K d) * vandermondeProd (centeredRootIn K d) →
      ¬ ∃ t : centeredCoeffField K d, e * c = t * t) :
    (L ≃ₐ[rootField (centeredCoeffField K d) (L := L)
        (Polynomial.X ^ (2 * m) - Polynomial.C c)] L) ≃* Equiv.Perm (Fin d) := by
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

/-- **The odd base change theorem for the centered polynomial, in any ambient.** -/
noncomputable def centeredRadicalBaseChangeOddIn (hd : 2 ≤ d)
    {c : centeredCoeffField K d} {n : ℕ} (hn : 0 < n)
    [Polynomial.IsSplittingField (centeredCoeffField K d) L
      (centeredMonicE K d * (Polynomial.X ^ n - Polynomial.C c))]
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c :
      Polynomial (centeredCoeffField K d)))
    (hodd : ¬ 2 ∣ n)
    (hdeg : ∀ α : L, α ^ n = algebraMap (centeredCoeffField K d) L c →
      n ≤ Module.finrank (centeredCoeffField K d)
        (IntermediateField.adjoin (centeredCoeffField K d) {α})) :
    (L ≃ₐ[rootField (centeredCoeffField K d) (L := L)
        (Polynomial.X ^ n - Polynomial.C c)] L) ≃* Equiv.Perm (Fin d) := by
  haveI : CharZero (centeredCoeffField K d) :=
    charZero_of_injective_algebraMap (algebraMap K (centeredCoeffField K d)).injective
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  exact radicalBaseChangeOddFromDegree centeredMonicE_ne_zero hn
    (centeredGaloisEquiv K d).symm
    (primitiveRoots_nonempty_of_algebra K (centeredCoeffField K d) hn)
    hirr hodd hdeg

end GaloisForLFunctions.HTGeometry
