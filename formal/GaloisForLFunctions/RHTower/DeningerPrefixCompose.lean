import GaloisForLFunctions.RHTower.DeningerRotate

/-!
# Composing the prefixes of successive rotations

Rotating by `t₀` and then by `t₁` rotates by `t₀ + t₁`, and the prefix moved by the composite is the
prefix moved by the first followed by the prefix moved by the second.  Reduced modulo the length of
the word, the whole copies of the word that are passed become factors of its product.

* `deningerPrefix_compose` : the product of the two prefixes, modulo whole copies.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **Composing the prefixes of successive rotations.**  The prefix moved by a rotation by `t₀`
followed by the prefix moved by a rotation by `t₁` of the rotated word is the prefix moved by the
rotation by `t₀ + t₁`, whole copies of the word contributing powers of its product. -/
theorem deningerPrefix_compose (U : List (Σ i, G i)) (t₀ t₁ : ℕ) (ht₀ : t₀ ≤ U.length)
    (ht₁ : t₁ ≤ U.length) :
    ∃ δ : ℕ, deningerLetterProd (φ := φ) (U.take t₀) *
        deningerLetterProd (φ := φ) ((U.rotate t₀).take t₁) =
      deningerLetterProd (φ := φ) U ^ δ *
        deningerLetterProd (φ := φ) (U.take ((t₀ + t₁) % U.length)) := by
  classical
  rcases Nat.eq_zero_or_pos U.length with hL | hLpos
  · have hU : U = [] := List.eq_nil_of_length_eq_zero hL
    subst hU
    exact ⟨0, by simp⟩
  have hrot : U.rotate t₀ = U.drop t₀ ++ U.take t₀ := List.rotate_eq_drop_append_take ht₀
  have hdroplen : (U.drop t₀).length = U.length - t₀ := List.length_drop
  rcases Nat.lt_or_ge U.length (t₀ + t₁) with hlt | hle
  · -- the composite prefix passes one whole copy of the word
    have h1 : (U.rotate t₀).take t₁ = U.drop t₀ ++ (U.take t₀).take (t₁ - (U.length - t₀)) := by
      rw [hrot, List.take_append, hdroplen, List.take_of_length_le (by omega)]
    have h2 : (U.take t₀).take (t₁ - (U.length - t₀)) = U.take (t₀ + t₁ - U.length) := by
      rw [List.take_take, min_eq_left (by omega)]
      congr 1
      omega
    have h3 : deningerLetterProd (φ := φ) (U.take t₀) * deningerLetterProd (φ := φ) (U.drop t₀) =
        deningerLetterProd (φ := φ) U := (deningerLetterProd_take_drop U t₀).symm
    rcases eq_or_lt_of_le (show t₀ + t₁ ≤ 2 * U.length by omega) with heq2 | hlt2
    · refine ⟨2, ?_⟩
      have ht : t₀ + t₁ - U.length = U.length := by omega
      have hmod : (t₀ + t₁) % U.length = 0 := by
        rw [heq2, Nat.mul_mod_left]
      rw [h1, h2, ht, hmod, List.take_zero, deningerLetterProd_nil, mul_one,
        deningerLetterProd_append, ← mul_assoc, h3, List.take_length, sq]
    · refine ⟨1, ?_⟩
      have hmod : (t₀ + t₁) % U.length = t₀ + t₁ - U.length := by
        rw [show t₀ + t₁ = U.length + (t₀ + t₁ - U.length) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)]
        omega
      rw [h1, h2, hmod, deningerLetterProd_append, ← mul_assoc, h3, pow_one]
  · -- the composite prefix is a prefix of the word
    have h1 : (U.rotate t₀).take t₁ = (U.drop t₀).take t₁ := by
      rw [hrot, List.take_append, show t₁ - (U.drop t₀).length = 0 by omega, List.take_zero,
        List.append_nil]
    have h2 : U.take t₀ ++ (U.drop t₀).take t₁ = U.take (t₀ + t₁) := List.take_add.symm
    rcases eq_or_lt_of_le hle with heq | hlt2
    · refine ⟨1, ?_⟩
      rw [h1, ← deningerLetterProd_append, h2, heq, List.take_length, Nat.mod_self,
        List.take_zero, deningerLetterProd_nil, mul_one, pow_one]
    · refine ⟨0, ?_⟩
      rw [h1, ← deningerLetterProd_append, h2, Nat.mod_eq_of_lt hlt2, pow_zero, one_mul]

end RHTower
