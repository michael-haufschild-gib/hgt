/-
Doc 24 AMP copy/flip transition bookkeeping for the SPUR-R stack.

`SpurCounting` proves the corrected zero-count arithmetic once the number `T`
of copy/flip crossings is supplied.  This module supplies the finite sequence
side: a concrete transition count for ordered copy/flip states and the single
block-switch bound consumed by the corrected counting lemma.
-/
import GaloisForLFunctions.RHTower.SpurCounting

namespace RHTower

/-- Number of adjacent copy/flip state changes in an ordered critical list. -/
def copyFlipTransitions : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => (if x = y then 0 else 1) + copyFlipTransitions (y :: xs)

@[simp] theorem copyFlipTransitions_nil : copyFlipTransitions [] = 0 := rfl

@[simp] theorem copyFlipTransitions_singleton (b : Bool) : copyFlipTransitions [b] = 0 := rfl

@[simp] theorem copyFlipTransitions_cons_cons (x y : Bool) (xs : List Bool) :
    copyFlipTransitions (x :: y :: xs) =
      (if x = y then 0 else 1) + copyFlipTransitions (y :: xs) := rfl

/-- A constant copy/flip run has no internal transitions. -/
theorem copyFlipTransitions_cons_replicate_same (n : ℕ) (b : Bool) :
    copyFlipTransitions (b :: List.replicate n b) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, copyFlipTransitions_cons_cons, if_pos rfl, zero_add, ih]

/-- A replicated constant copy/flip run has no transitions. -/
@[simp] theorem copyFlipTransitions_replicate (n : ℕ) (b : Bool) :
    copyFlipTransitions (List.replicate n b) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [List.replicate_succ]
      exact copyFlipTransitions_cons_replicate_same n b

/-- A leading state followed by a constant run of the opposite state has at most one transition. -/
theorem copyFlipTransitions_cons_replicate_not_le_one (m : ℕ) (b : Bool) :
    copyFlipTransitions (b :: List.replicate m (!b)) ≤ 1 := by
  cases m with
  | zero => simp
  | succ m =>
      rw [List.replicate_succ, copyFlipTransitions_cons_cons]
      have hne : b ≠ !b := by cases b <;> simp
      rw [if_neg hne]
      have hsame := copyFlipTransitions_cons_replicate_same m (!b)
      rw [hsame]

/-- A single copy/flip block switch has at most one adjacent transition. -/
theorem copyFlipTransitions_block_le_one (n m : ℕ) (b : Bool) :
    copyFlipTransitions (List.replicate n b ++ List.replicate m (!b)) ≤ 1 := by
  cases n with
  | zero => simp
  | succ n =>
      induction n with
      | zero =>
          simpa using copyFlipTransitions_cons_replicate_not_le_one m b
      | succ n ih =>
          rw [List.replicate_succ]
          rw [List.replicate_succ]
          change copyFlipTransitions
            (b :: b :: (List.replicate n b ++ List.replicate m (!b))) ≤ 1
          rw [copyFlipTransitions_cons_cons, if_pos rfl, zero_add]
          exact ih

/-- Corrected counting for a concrete copy/flip sequence with a single block switch.

This is doc 24's finite tail with `T` instantiated as the actual transition count of
the ordered copy/flip states. -/
theorem corrected_counting_exact_pair_of_copyFlip_block {Z n m : ℕ} {b : Bool}
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (List.replicate n b ++ List.replicate m (!b))) :
    Z = 2 :=
  even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_at_most_one_crossing hbound
      (copyFlipTransitions_block_le_one n m b) heven)

end RHTower
