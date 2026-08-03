import GaloisForLFunctions.RHTower.DeningerPowWord

/-!
# Rotation is conjugation

Rotating a word conjugates its product by the prefix that is moved to the end.  This is what makes
the comparison of powers in an amalgam conclusive: the comparison yields that two cyclically reduced
words are rotations of one another, and rotation being conjugation turns that into an equality of
the original elements.

* `deningerLetterProd_rotate` : rotating a word conjugates its product.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

theorem deningerLetterProd_take_drop (V : List (Σ i, G i)) (t : ℕ) :
    deningerLetterProd (φ := φ) V =
      deningerLetterProd (φ := φ) (V.take t) * deningerLetterProd (φ := φ) (V.drop t) := by
  rw [← deningerLetterProd_append, List.take_append_drop]

/-- **Rotation is conjugation.**  Rotating a word by `t` conjugates its product by the prefix of
length `t`. -/
theorem deningerLetterProd_rotate (V : List (Σ i, G i)) (t : ℕ) (ht : t ≤ V.length) :
    deningerLetterProd (φ := φ) (V.rotate t) =
      (deningerLetterProd (φ := φ) (V.take t))⁻¹ * deningerLetterProd (φ := φ) V *
        deningerLetterProd (φ := φ) (V.take t) := by
  rw [List.rotate_eq_drop_append_take ht, deningerLetterProd_append,
    deningerLetterProd_take_drop V t]
  group

/-- A rotation of a word is conjugate to the word by the prefix that was moved. -/
theorem deningerLetterProd_rotate_conj (V : List (Σ i, G i)) (t : ℕ) (ht : t ≤ V.length) :
    deningerLetterProd (φ := φ) (V.take t) * deningerLetterProd (φ := φ) (V.rotate t) *
        (deningerLetterProd (φ := φ) (V.take t))⁻¹ = deningerLetterProd (φ := φ) V := by
  rw [deningerLetterProd_rotate V t ht]
  group

end RHTower
