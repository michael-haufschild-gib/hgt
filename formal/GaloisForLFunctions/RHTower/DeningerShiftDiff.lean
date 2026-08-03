import GaloisForLFunctions.RHTower.DeningerBaseHeadSuffix

/-!
# Two shifts producing the same word

Shifting a base element through a word produces a new base element and a new word.  When two shifts
produce the same word, the difference of the two base elements is conjugated by the word into the
difference of the two new ones: the common word cancels on the right.  This is the step which turns
a comparison of the heads of two powers into a statement about conjugating the base group.

* `deningerShift_diff` : the conjugation identity.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **Two shifts producing the same word conjugate the difference of their base elements.** -/
theorem deningerShift_diff (M M₁ : List (Σ i, G i)) (a b a' b' : H)
    (h1 : deningerLetterProd (φ := φ) M * PushoutI.base φ a =
      PushoutI.base φ a' * deningerLetterProd (φ := φ) M₁)
    (h2 : deningerLetterProd (φ := φ) M * PushoutI.base φ b =
      PushoutI.base φ b' * deningerLetterProd (φ := φ) M₁) :
    deningerLetterProd (φ := φ) M * PushoutI.base φ (a * b⁻¹) *
        (deningerLetterProd (φ := φ) M)⁻¹ =
      PushoutI.base φ (a' * b'⁻¹) := by
  rw [map_mul, map_inv, map_mul, map_inv]
  calc deningerLetterProd (φ := φ) M * (PushoutI.base φ a * (PushoutI.base φ b)⁻¹) *
        (deningerLetterProd (φ := φ) M)⁻¹
      = (deningerLetterProd (φ := φ) M * PushoutI.base φ a) *
        (deningerLetterProd (φ := φ) M * PushoutI.base φ b)⁻¹ := by group
    _ = (PushoutI.base φ a' * deningerLetterProd (φ := φ) M₁) *
        (PushoutI.base φ b' * deningerLetterProd (φ := φ) M₁)⁻¹ := by rw [h1, h2]
    _ = PushoutI.base φ a' * (PushoutI.base φ b')⁻¹ := by group

end RHTower
