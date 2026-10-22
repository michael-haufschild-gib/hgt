import GaloisForLFunctions.RHTower.Deninger.DeningerPrefixTransfer

/-!
# Transferring a prefix across a changed tail

A prefix that stops inside the common part of two words transfers between them, and the suffixes it
leaves begin in the same factor as soon as the changed tails do.  This covers both cases of a
cyclic reduction step: the tail may be replaced by one letter, or by two.

* `deningerPrefix_transfer'` : the prefix transfers.
* `deningerHead_map_fst_of_append'` : the suffixes begin in the same factor.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*}

theorem deningerPrefix_take (C R M T : List (Σ i, G i)) (h : C ++ R = M ++ T)
    (hle : C.length ≤ M.length) : C = M.take C.length := by
  set n := C.length with hn
  have hCa : C = (M ++ T).take n := by
    rw [← h, hn, List.take_left]
  rw [hCa, List.take_append_of_le_length hle]

/-- **The prefix transfers.** -/
theorem deningerPrefix_transfer' (C M T' : List (Σ i, G i)) (hle : C.length ≤ M.length)
    (h : C = M.take C.length) :
    C ++ ((M ++ T').drop C.length) = M ++ T' := by
  set n := C.length with hn
  have hC : (M ++ T').take n = C := by
    rw [List.take_append_of_le_length hle, ← h]
  rw [← hC, List.take_append_drop]

/-- **The suffixes begin in the same factor.** -/
theorem deningerHead_map_fst_of_append' (C R R' M T T' : List (Σ i, G i))
    (h1 : C ++ R = M ++ T) (h2 : C ++ R' = M ++ T') (hle : C.length ≤ M.length)
    (hT : T.head?.map Sigma.fst = T'.head?.map Sigma.fst) :
    R.head?.map Sigma.fst = R'.head?.map Sigma.fst := by
  have hR : R = (M ++ T).drop C.length := by rw [← h1, List.drop_left]
  have hR' : R' = (M ++ T').drop C.length := by rw [← h2, List.drop_left]
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hdrop : ∀ X : List (Σ i, G i), (M ++ X).drop C.length = M.drop C.length ++ X :=
      fun X => List.drop_append_of_le_length (le_of_lt hlt)
    have hMne : M.drop C.length ≠ [] := by
      intro hnil
      have hlen : (M.drop C.length).length = M.length - C.length :=
        List.length_drop (l := M) (i := C.length)
      rw [hnil] at hlen
      simp at hlen
      omega
    rw [hR, hR', hdrop, hdrop, List.head?_append_of_ne_nil _ hMne,
      List.head?_append_of_ne_nil _ hMne]
  · have hdrop : ∀ X : List (Σ i, G i), (M ++ X).drop C.length = X := fun X => by
      rw [heq, List.drop_left]
    rw [hR, hR', hdrop, hdrop]
    exact hT

end RHTower
