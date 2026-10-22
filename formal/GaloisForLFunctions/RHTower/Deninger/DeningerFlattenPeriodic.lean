import GaloisForLFunctions.RHTower.Deninger.DeningerRotateCycRed

/-!
# Periodicity of a repeated word

Repeating a word makes it periodic: rotating the repetition by the length of the word gives it back.

* `deningerFlatten_snoc` : the repetition, built from the right.
* `deningerFlatten_rotate_length` : the periodicity.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

omit [∀ i, Group (G i)] in
/-- A word commutes with its repetitions. -/
theorem deningerFlatten_comm (L : List (Σ i, G i)) (n : ℕ) :
    deningerFlatten (G := G) L n ++ L = L ++ deningerFlatten (G := G) L n := by
  induction n with
  | zero => simp [deningerFlatten]
  | succ n ih =>
    rw [deningerFlatten_succ, List.append_assoc, ih]

omit [∀ i, Group (G i)] in
/-- The repetition, built from the right. -/
theorem deningerFlatten_snoc (L : List (Σ i, G i)) (n : ℕ) :
    deningerFlatten (G := G) L (n + 1) = deningerFlatten (G := G) L n ++ L := by
  rw [deningerFlatten_succ, deningerFlatten_comm]

omit [∀ i, Group (G i)] in
/-- **Repeating a word makes it periodic.** -/
theorem deningerFlatten_rotate_length (L : List (Σ i, G i)) (n : ℕ) :
    (deningerFlatten (G := G) L n).rotate L.length = deningerFlatten (G := G) L n := by
  cases n with
  | zero => simp [deningerFlatten]
  | succ n =>
    rw [deningerFlatten_succ,
      List.rotate_eq_drop_append_take (by simp), List.drop_left, List.take_left]
    exact (deningerFlatten_snoc L n).symm

end RHTower
