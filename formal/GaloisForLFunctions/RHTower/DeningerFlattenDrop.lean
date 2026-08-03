import GaloisForLFunctions.RHTower.DeningerFlattenRotate

/-!
# Dropping whole and partial copies

Dropping a multiple of the length of a word from a concatenation of copies removes whole copies;
dropping a further partial amount rotates the word.  Together with injectivity of the concatenation
these are the list ingredients of the comparison of powers.

* `deningerFlatten_inj` : a concatenation of copies determines the word.
* `deningerDrop_mul_flatten` : dropping whole copies.
* `deningerDrop_flatten_succ` : dropping a partial copy.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*}

/-- A concatenation of copies determines the word, given its length. -/
theorem deningerFlatten_inj (A B : List (Σ i, G i)) (K : ℕ)
    (h : deningerFlatten (G := G) A (K + 1) = deningerFlatten (G := G) B (K + 1))
    (hlen : A.length = B.length) : A = B := by
  rw [deningerFlatten_succ, deningerFlatten_succ] at h
  exact List.append_inj_left h hlen

/-- Dropping a multiple of the length removes whole copies. -/
theorem deningerDrop_mul_flatten (V : List (Σ i, G i)) (q M : ℕ) (hq : q ≤ M) :
    (deningerFlatten (G := G) V M).drop (q * V.length) =
      deningerFlatten (G := G) V (M - q) := by
  induction q generalizing M with
  | zero => simp
  | succ q ih =>
    obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    rw [deningerFlatten_succ, show (q + 1) * V.length = V.length + q * V.length by ring,
      List.drop_append,
      List.drop_eq_nil_of_le (by omega : V.length ≤ V.length + q * V.length),
      List.nil_append, show V.length + q * V.length - V.length = q * V.length by omega,
      ih m (by omega)]
    congr 1
    omega

/-- Dropping a partial copy rotates the word. -/
theorem deningerDrop_flatten_succ (V : List (Σ i, G i)) (r : ℕ) (hr : r ≤ V.length) (k : ℕ) :
    (deningerFlatten (G := G) V (k + 1)).drop r =
      deningerFlatten (G := G) (V.rotate r) k ++ V.drop r := by
  rw [deningerFlatten_succ, List.drop_append_of_le_length hr, deningerDrop_flatten V r hr]

end RHTower
