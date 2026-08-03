import GaloisForLFunctions.RHTower.DeningerRotate

/-!
# Dropping letters from a concatenation of copies

Dropping a prefix from a concatenation of copies of a word gives a concatenation of copies of the
rotated word, followed by the dropped-from tail.  This is the combinatorial identity behind the
appearance of rotations when powers are compared.

* `deningerDrop_append` : dropping and reattaching a word.
* `deningerDrop_flatten` : dropping from a concatenation of copies.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*}

theorem deningerDrop_append (V : List (Σ i, G i)) (r : ℕ) (hr : r ≤ V.length) :
    V.drop r ++ V = V.rotate r ++ V.drop r := by
  rw [List.rotate_eq_drop_append_take hr, List.append_assoc, List.take_append_drop]

/-- **Dropping from a concatenation of copies.** -/
theorem deningerDrop_flatten (V : List (Σ i, G i)) (r : ℕ) (hr : r ≤ V.length) (k : ℕ) :
    V.drop r ++ deningerFlatten (G := G) V k =
      deningerFlatten (G := G) (V.rotate r) k ++ V.drop r := by
  induction k with
  | zero => simp [deningerFlatten]
  | succ k ih =>
    rw [deningerFlatten_succ, deningerFlatten_succ, ← List.append_assoc,
      deningerDrop_append V r hr, List.append_assoc, ih, ← List.append_assoc]

end RHTower
