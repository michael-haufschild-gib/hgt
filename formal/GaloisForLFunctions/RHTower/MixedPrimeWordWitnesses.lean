import GaloisForLFunctions.RHTower.PrimeWordSupportSelector

/-!
# Realizations of the mixed prime-word interface

A word is mixed when its letter support has at least two elements, so any two-letter word with
distinct letters realizes the interface, and mixedness is inherited by every extension of such a
word.
-/

namespace GaloisForLFunctions

variable {α : Type*} [DecidableEq α]

/-- A two-letter word with distinct letters is mixed. -/
theorem isMixedPrimeWord_pair {x y : α} (h : x ≠ y) : IsMixedPrimeWord [x, y] := by
  rw [IsMixedPrimeWord, primeWordSupport]
  rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
  simp [Finset.card_insert_of_notMem, h]

end GaloisForLFunctions
