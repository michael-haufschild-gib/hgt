import GaloisForLFunctions.RHTower.DeningerWordUnique

/-!
# The form of a conjugating letter

A letter which conjugates a cyclically reduced word to a rotation of it is the inverse of the letter
that moves, up to the base group: at the front it is the inverse first letter, at the back it is the
last letter.  These are the two steps by which a conjugating element is a prefix of the periodic
word.

* `deningerConjLetter_front` : the front form.
* `deningerConjLetter_back` : the back form.
* `deningerBase_mul_inv_letterProd` : the base group absorbs into an inverted word.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **A letter cancelling the front letter is its inverse, up to the base group.** -/
theorem deningerConjLetter_front (i : ι) (x u₁ : G i) (k : H) (hk : x * u₁ = φ i k) :
    PushoutI.of (φ := φ) i x =
      PushoutI.base φ k * (PushoutI.of (φ := φ) i u₁)⁻¹ := by
  have hx : x = φ i k * u₁⁻¹ := by rw [← hk]; group
  rw [hx, map_mul, PushoutI.of_apply_eq_base, map_inv]

/-- **A letter cancelling the last letter is that letter, up to the base group.** -/
theorem deningerConjLetter_back (i : ι) (x uℓ : G i) (k : H) (hk : uℓ * x⁻¹ = φ i k) :
    PushoutI.of (φ := φ) i x =
      (PushoutI.base φ k)⁻¹ * PushoutI.of (φ := φ) i uℓ := by
  have hx : x = (φ i k)⁻¹ * uℓ := by rw [← hk]; group
  rw [hx, map_mul, ← map_inv, PushoutI.of_apply_eq_base, map_inv]

/-- The base group absorbs into an inverted letter. -/
theorem deningerBase_mul_inv_of (i : ι) (x : G i) (m : H) :
    PushoutI.base φ m * (PushoutI.of (φ := φ) i x)⁻¹ =
      (PushoutI.of (φ := φ) i (x * (φ i m)⁻¹))⁻¹ := by
  rw [map_mul, map_inv, PushoutI.of_apply_eq_base, mul_inv_rev, inv_inv]

/-- **The base group absorbs into the last letter of an inverted word.**  This is what keeps a
conjugator, built up by cancelling letters one at a time, inside the class of inverted words. -/
theorem deningerBase_mul_inv_letterProd (P : List (Σ i, G i)) (p : Σ i, G i) (m : H) :
    PushoutI.base φ m * (deningerLetterProd (φ := φ) (P ++ [p]))⁻¹ =
      (deningerLetterProd (φ := φ)
        (P ++ [(⟨p.1, p.2 * φ p.1 m⁻¹⟩ : Σ i, G i)]))⁻¹ := by
  rw [← deningerLetterProd_mul_base_snoc P p m⁻¹, map_inv, mul_inv_rev, inv_inv]

end RHTower
