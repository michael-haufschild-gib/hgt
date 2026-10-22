import GaloisForLFunctions.RHTower.Deninger.DeningerConjLetterCases

/-!
# The length of a rotation

A rotation of a cyclically reduced word has the length of the word, and conjugating by the base
group does not change it.  So a conjugation which is a rotation up to the base group does not change
the length either.

* `deningerLen_rotate_baseConj` : the length of a base conjugate of a rotation.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A base conjugate of a rotation has the length of the word.** -/
theorem deningerLen_rotate_baseConj (U : List (Σ i, G i))
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (t : ℕ) (ht : t ≤ U.length) (m : H) :
    deningerLen d (PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) *
      (PushoutI.base φ m)⁻¹) = U.length := by
  obtain ⟨hrred, hralt, _⟩ := deningerRotate_cycRed (φ := φ) U hred halt hcyc t ht
  have hlen := congrArg List.length
    (deningerNormalWord_map_fst (d := d) (U.rotate t) hrred hralt)
  rw [List.length_map, List.length_map, List.length_rotate] at hlen
  rw [← map_inv, deningerLen_base_conj]
  show ((_ • (NormalWord.empty : NormalWord d)) : NormalWord d).toList.length = _
  exact hlen

end RHTower
