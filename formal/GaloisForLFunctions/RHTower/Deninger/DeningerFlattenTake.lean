import GaloisForLFunctions.RHTower.Deninger.DeningerFlattenPeriodic

/-!
# Prefixes of a repeated word

A prefix of a repetition is a whole number of copies followed by a prefix of the word.

* `deningerFlatten_take` : the prefix.
* `deningerRotate_flatten_conj` : a rotation of a power is a conjugate by a prefix of the word.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

omit [∀ i, Group (G i)] in
/-- **A prefix of a repetition is a whole number of copies followed by a prefix of the word.** -/
theorem deningerFlatten_take (L : List (Σ i, G i)) (r : ℕ) (hr : r ≤ L.length) :
    ∀ q n : ℕ, q < n →
      (deningerFlatten (G := G) L n).take (q * L.length + r) =
        deningerFlatten (G := G) L q ++ L.take r := by
  intro q
  induction q with
  | zero =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [deningerFlatten_succ]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [List.take_append_of_le_length hr]
    simp [deningerFlatten]
  | succ q ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [deningerFlatten_succ,
      show (q + 1) * L.length + r = L.length + (q * L.length + r) by ring,
      List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      ih n' (by omega), deningerFlatten_succ, List.append_assoc]

/-- The product of a prefix of a repetition. -/
theorem deningerLetterProd_take_flatten (L : List (Σ i, G i)) (r : ℕ) (hr : r ≤ L.length)
    (q n : ℕ) (hq : q < n) :
    deningerLetterProd (φ := φ) ((deningerFlatten (G := G) L n).take (q * L.length + r)) =
      (deningerLetterProd (φ := φ) L) ^ q * deningerLetterProd (φ := φ) (L.take r) := by
  rw [deningerFlatten_take L r hr q n hq, deningerLetterProd_append, deningerLetterProd_flatten]

/-- **A rotation of a power is a conjugate of that power by a prefix of the word.**  The whole
copies in the rotation commute with the power and drop out. -/
theorem deningerRotate_flatten_conj (L : List (Σ i, G i)) (r : ℕ) (hr : r ≤ L.length)
    (q n : ℕ) (hq : q < n) :
    deningerLetterProd (φ := φ)
        ((deningerFlatten (G := G) L n).rotate (q * L.length + r)) =
      (deningerLetterProd (φ := φ) (L.take r))⁻¹ * (deningerLetterProd (φ := φ) L) ^ n *
        deningerLetterProd (φ := φ) (L.take r) := by
  have hle : q * L.length + r ≤ (deningerFlatten (G := G) L n).length := by
    rw [deningerFlatten_length]
    have : (q + 1) * L.length ≤ n * L.length := Nat.mul_le_mul_right _ (by omega)
    nlinarith [Nat.zero_le (q * L.length)]
  rw [deningerLetterProd_rotate _ _ hle, deningerLetterProd_take_flatten L r hr q n hq,
    deningerLetterProd_flatten]
  group

end RHTower
