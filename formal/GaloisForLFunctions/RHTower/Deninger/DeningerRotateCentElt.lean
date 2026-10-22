import GaloisForLFunctions.RHTower.Deninger.DeningerRotate
import GaloisForLFunctions.RHTower.Deninger.DeningerBaseLength

/-!
# The element realizing a rotation symmetry

Rotation is conjugation by the prefix that is moved, so a rotation symmetry of a cyclically reduced
word says that the prefix, corrected by the base element of the symmetry, commutes with the product
of the word.  Its length is the length of the rotation, because the base group does not change
lengths.

* `deningerRotateCentElt` : the element realizing the symmetry.
* `deningerRotateCentElt_comm` : it commutes with the product of the word.
* `deningerRotateCentElt_len` : its length is the length of the rotation.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- The element realizing a rotation symmetry: the prefix moved by the rotation, corrected by the
base element of the symmetry. -/
def deningerRotateCentElt (φ : ∀ i, H →* G i) (U : List (Σ i, G i)) (t : ℕ) (m : H) :
    PushoutI φ :=
  deningerLetterProd (φ := φ) (U.take t) * (PushoutI.base φ m)⁻¹

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **The element of a rotation symmetry commutes with the word.** -/
theorem deningerRotateCentElt_comm (U : List (Σ i, G i)) (t : ℕ) (ht : t ≤ U.length) (m : H)
    (hrot : deningerLetterProd (φ := φ) U =
      PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) * (PushoutI.base φ m)⁻¹) :
    (deningerRotateCentElt φ U t m)⁻¹ * deningerLetterProd (φ := φ) U *
      deningerRotateCentElt φ U t m = deningerLetterProd (φ := φ) U := by
  rw [deningerRotateCentElt]
  calc (deningerLetterProd (φ := φ) (U.take t) * (PushoutI.base φ m)⁻¹)⁻¹ *
        deningerLetterProd (φ := φ) U *
        (deningerLetterProd (φ := φ) (U.take t) * (PushoutI.base φ m)⁻¹)
      = PushoutI.base φ m * ((deningerLetterProd (φ := φ) (U.take t))⁻¹ *
          deningerLetterProd (φ := φ) U * deningerLetterProd (φ := φ) (U.take t)) *
          (PushoutI.base φ m)⁻¹ := by group
    _ = PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) *
          (PushoutI.base φ m)⁻¹ := by rw [deningerLetterProd_rotate U t ht]
    _ = deningerLetterProd (φ := φ) U := hrot.symm

include d in
/-- **The length of the element of a rotation symmetry is the length of the rotation.** -/
theorem deningerRotateCentElt_len (U : List (Σ i, G i))
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (t : ℕ) (ht : t ≤ U.length) (m : H) :
    deningerLen d (deningerRotateCentElt φ U t m) = t := by
  have hbase : (PushoutI.base φ m)⁻¹ = PushoutI.base φ m⁻¹ := (map_inv _ _).symm
  rw [deningerRotateCentElt, hbase, deningerLen_mul_base,
    deningerLen_letterProd (d := d) (U.take t)
      (fun p hp => hred p (List.take_subset t U hp)) (halt.take t),
    List.length_take, min_eq_left ht]

end RHTower
