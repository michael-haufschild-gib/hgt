import GaloisForLFunctions.RHTower.Deninger.DeningerCycData

/-!
# Suffixes of words differing in their last letter

Two words with a common prefix that differ only in their last letter have suffixes beginning in the
same factor, provided the differing letters lie in the same factor.  This is the index bookkeeping
of the cyclic reduction recursion: a reduction step changes only the tail of the word.

* `deningerHead_map_fst_of_append` : the suffixes begin in the same factor.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*}

/-- **The suffixes begin in the same factor.** -/
theorem deningerHead_map_fst_of_append (C R R' M : List (Σ i, G i)) (a b : Σ i, G i)
    (h1 : C ++ R = M ++ [a]) (h2 : C ++ R' = M ++ [b]) (hab : a.1 = b.1) (hne : R ≠ []) :
    R.head?.map Sigma.fst = R'.head?.map Sigma.fst := by
  have hR : R = (M ++ [a]).drop C.length := by
    rw [← h1, List.drop_left]
  have hR' : R' = (M ++ [b]).drop C.length := by
    rw [← h2, List.drop_left]
  rcases lt_trichotomy C.length M.length with hlt | heq | hgt
  · have hdrop : ∀ x : Σ i, G i, (M ++ [x]).drop C.length = M.drop C.length ++ [x] := fun x => by
      rw [List.drop_append_of_le_length (le_of_lt hlt)]
    have hMne : M.drop C.length ≠ [] := by
      intro hnil
      have hlen : (M.drop C.length).length = M.length - C.length :=
        List.length_drop (l := M) (i := C.length)
      rw [hnil] at hlen
      simp at hlen
      omega
    rw [hR, hR', hdrop, hdrop, List.head?_append_of_ne_nil _ hMne,
      List.head?_append_of_ne_nil _ hMne]
  · have hdrop : ∀ x : Σ i, G i, (M ++ [x]).drop C.length = [x] := fun x => by
      rw [heq, List.drop_append_of_le_length (le_of_eq rfl)]
      simp
    rw [hR, hR', hdrop, hdrop]
    simp [hab]
  · exfalso
    refine hne ?_
    rw [hR, List.drop_eq_nil_of_le]
    simp
    omega

end RHTower
