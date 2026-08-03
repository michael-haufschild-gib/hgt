import GaloisForLFunctions.RHTower.DeningerSuffixIndex

/-!
# Transferring a prefix between words differing in their last letter

A prefix of a word is also a prefix of any word with the same letters except the last, and the
corresponding suffixes have the same length.  This is the list surgery the cyclic reduction
recursion performs when it reassembles the conjugator and the tail.

* `deningerPrefix_le` : a prefix leaving a nonempty suffix does not reach the last letter.
* `deningerPrefix_transfer` : the prefix transfers.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*}

theorem deningerPrefix_le (C R M : List (Σ i, G i)) (a : Σ i, G i)
    (h : C ++ R = M ++ [a]) (hR : R ≠ []) : C.length ≤ M.length := by
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hRpos : 0 < R.length := List.length_pos_iff.2 hR
  omega

/-- **The prefix transfers.** -/
theorem deningerPrefix_transfer (C R M : List (Σ i, G i)) (a b : Σ i, G i)
    (h : C ++ R = M ++ [a]) (hR : R ≠ []) :
    C ++ ((M ++ [b]).drop C.length) = M ++ [b] := by
  have hle := deningerPrefix_le C R M a h hR
  set n := C.length with hn
  have hCa : C = (M ++ [a]).take n := by
    rw [← h, hn, List.take_left]
  have hCM : C = M.take n := by
    rw [hCa, List.take_append_of_le_length hle]
  have hCb : (M ++ [b]).take n = C := by
    rw [List.take_append_of_le_length hle, hCM]
  rw [← hCb, List.take_append_drop]

/-- The suffixes have the same length. -/
theorem deningerSuffix_length (C R M : List (Σ i, G i)) (a b : Σ i, G i)
    (h : C ++ R = M ++ [a]) (hR : R ≠ []) :
    ((M ++ [b]).drop C.length).length = R.length := by
  have hle := deningerPrefix_le C R M a h hR
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil]
  omega

end RHTower
