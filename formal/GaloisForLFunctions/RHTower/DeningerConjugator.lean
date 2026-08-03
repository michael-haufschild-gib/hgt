import GaloisForLFunctions.RHTower.DeningerRotateLen

/-!
# The conjugator of a single letter

A single letter conjugating a cyclically reduced word of at least two letters to something no longer
than itself is, up to the base group, an inverted single letter: the letter it cancelled against.
This is the base case of the reconstruction of a conjugator from the rotation it induces.

* `deningerConjugator_letter` : the conjugator of a single letter.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A single conjugating letter is an inverted letter of the word, up to the base group.** -/
theorem deningerConjugator_letter (U : List (Σ i, G i)) (hlen2 : 2 ≤ U.length)
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (i : ι) (x : G i) (hx : x ∉ (φ i).range)
    (hshort : deningerLen d (PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
      (PushoutI.of (φ := φ) i x)⁻¹) ≤ U.length) :
    ∃ (y : G i) (m : H),
      PushoutI.of (φ := φ) i x =
        PushoutI.base φ m * (deningerLetterProd (φ := φ) [(⟨i, y⟩ : Σ i, G i)])⁻¹ := by
  rcases deningerConj_letter_cases (d := d) U hlen2 hred halt hcyc i x hx hshort with
    ⟨k, u₁, U', hUeq, hk⟩ | ⟨k, uℓ, U₀, hUeq, hk⟩
  · refine ⟨u₁, k, ?_⟩
    rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
    exact deningerConjLetter_front i x u₁ k hk
  · refine ⟨uℓ⁻¹, k⁻¹, ?_⟩
    rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
    show PushoutI.of (φ := φ) i x =
      PushoutI.base φ k⁻¹ * (PushoutI.of (φ := φ) i uℓ⁻¹)⁻¹
    rw [map_inv, map_inv, inv_inv]
    exact deningerConjLetter_back i x uℓ k hk

end RHTower
