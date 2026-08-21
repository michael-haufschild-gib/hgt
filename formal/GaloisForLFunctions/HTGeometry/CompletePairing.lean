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

end GaloisForLFunctions.HTGeometry
