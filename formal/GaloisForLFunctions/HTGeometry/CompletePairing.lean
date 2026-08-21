import GaloisForLFunctions.HTGeometry.ListPositionSum
import Mathlib.Algebra.Ring.Defs

/-!
# The complete-pairing sum of a word

For a symbol-valued kernel `c : α → α → K` the *complete-pairing sum* of a word `l : List α` is

```text
completePairing c l = ∑ over the perfect matchings M of the positions of l, ∏_{(i,j) ∈ M} c l[i] l[j]
```

written as the standard recursion: the first letter must be paired with one of the later letters,
and both are then deleted.  Words of odd length receive the value `0`, since the recursion runs out
of partners.

This is the scalar shadow of a Wick expansion: it is what survives when every normal-ordered product
of a nonempty word is annihilated, as it is by a vacuum expectation.
-/

universe u v

namespace GaloisForLFunctions.HTGeometry

variable {α : Type u} {K : Type v} [CommSemiring K]

/-- The sum over all perfect matchings of the positions of a word of the product of the kernel
values of the matched pairs, in recursive form. -/
def completePairing (c : α → α → K) : List α → K
  | [] => 1
  | (u :: t) => ∑ k : Fin t.length, c u t[(k : ℕ)] * completePairing c (t.eraseIdx (k : ℕ))
termination_by l => l.length
decreasing_by
  have h := List.length_eraseIdx_le t (k : ℕ)
  simp only [List.length_cons]
  omega

@[simp] theorem completePairing_nil (c : α → α → K) : completePairing c [] = 1 := by
  rw [completePairing]

/-- The head of a word must be paired with a later letter; both are then removed. -/
theorem completePairing_cons (c : α → α → K) (u : α) (t : List α) :
    completePairing c (u :: t) = positionSum t (fun a s => c u a * completePairing c s) := by
  rw [completePairing]
  rfl

@[simp] theorem completePairing_singleton (c : α → α → K) (u : α) :
    completePairing c [u] = 0 := by
  rw [completePairing_cons]
  simp

/-- A word of odd length has no perfect matching at all. -/
theorem completePairing_eq_zero_of_odd (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → Odd l.length → completePairing c l = 0 := by
  intro n
  induction n with
  | zero =>
      intro l hl hodd
      rw [Nat.odd_iff] at hodd
      omega
  | succ n ih =>
      intro l hl hodd
      match l with
      | [] => rw [Nat.odd_iff] at hodd; simp at hodd
      | (u :: t) =>
        rw [completePairing_cons]
        simp only [positionSum]
        refine Finset.sum_eq_zero fun k _ => ?_
        have hk := k.isLt
        have hlen : (t.eraseIdx (k : ℕ)).length = t.length - 1 :=
          List.length_eraseIdx_of_lt hk
        rw [Nat.odd_iff] at hodd
        simp only [List.length_cons] at hodd hl
        rw [ih _ (by omega) (by rw [Nat.odd_iff]; omega), mul_zero]

/-- The two-point value is the kernel itself. -/
@[simp] theorem completePairing_pair (c : α → α → K) (x y : α) :
    completePairing c [x, y] = c x y := by
  rw [completePairing_cons]
  simp [positionSum]

/-- **The four-point function has three terms**: the three ways of splitting four letters into two
pairs. -/
theorem completePairing_quadruple (c : α → α → K) (x y z w : α) :
    completePairing c [x, y, z, w] = c x y * c z w + c x z * c y w + c x w * c y z := by
  rw [completePairing_cons]
  simp only [positionSum, List.length_cons, List.length_nil, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil, completePairing_pair,
    add_zero]
  ring

end GaloisForLFunctions.HTGeometry
