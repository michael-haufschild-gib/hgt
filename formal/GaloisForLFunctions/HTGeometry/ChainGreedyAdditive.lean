import GaloisForLFunctions.HTGeometry.ChainGreedyLeft

/-!
# Additivity of the greedy scan across a separated split

```text
chainGreedy_union_of_sep       ** A left of S and every greedy element of A at distance ≥ 2 from S
                                  ⟹ chainGreedy (A ∪ S) = chainGreedy A ∪ chainGreedy S **
card_chainGreedy_union_of_sep  hence the counts add
```

The induction is on `A`: the minimum of `A ∪ S` is that of `A`, the separation hypothesis makes the
filter leave `S` untouched, and the filtered `A` inherits both hypotheses.

This is the additivity `γ(S ∪ A) = γ(A) + γ(S)` that shape I of the Cohen–Macaulay recursion needs:
when the least available vertex is at distance at least two from the last forced greedy element, the
complex on the available vertices is a plain chain complex with parameter `r − γ(A)`.
-/

namespace GaloisForLFunctions.HTGeometry

theorem chainGreedy_filter_subset {A : Finset ℕ} (h : A.Nonempty) :
    chainGreedy (A.filter (fun y => A.min' h + 2 ≤ y)) ⊆ chainGreedy A := by
  rw [chainGreedy_eq_insert h]
  exact Finset.subset_insert _ _

/-- **Additivity of the greedy scan across a separated left/right split.** -/
theorem chainGreedy_union_of_sep : ∀ (A S : Finset ℕ),
    (∀ a ∈ A, ∀ s ∈ S, a < s) →
    (∀ x ∈ chainGreedy A, ∀ s ∈ S, x + 2 ≤ s) →
    chainGreedy (A ∪ S) = chainGreedy A ∪ chainGreedy S := by
  classical
  intro A
  induction A using Finset.strongInduction with
  | _ A ih =>
    intro S hlt hsep
    by_cases hA : A.Nonempty
    · have hAS : (A ∪ S).Nonempty := hA.mono Finset.subset_union_left
      have hmin : (A ∪ S).min' hAS = A.min' hA := by
        refine le_antisymm ?_ ?_
        · exact Finset.min'_le _ _ (Finset.mem_union_left S (A.min'_mem hA))
        · refine Finset.le_min' _ _ _ ?_
          intro y hy
          rcases Finset.mem_union.mp hy with hy | hy
          · exact A.min'_le y hy
          · exact le_of_lt (hlt _ (A.min'_mem hA) _ hy)
      set m := A.min' hA with hm
      have hmg : m ∈ chainGreedy A := by
        rw [chainGreedy_eq_insert hA, ← hm]
        exact Finset.mem_insert_self _ _
      have hSfil : S.filter (fun y => m + 2 ≤ y) = S := by
        refine Finset.filter_true_of_mem ?_
        intro s hs
        exact hsep m hmg s hs
      have hfilter : (A ∪ S).filter (fun y => m + 2 ≤ y)
          = A.filter (fun y => m + 2 ≤ y) ∪ S := by
        rw [Finset.filter_union, hSfil]
      have hih : chainGreedy (A.filter (fun y => m + 2 ≤ y) ∪ S)
          = chainGreedy (A.filter (fun y => m + 2 ≤ y)) ∪ chainGreedy S := by
        refine ih _ (filter_ssubset hA) S ?_ ?_
        · intro a ha s hs
          exact hlt a (Finset.mem_of_mem_filter a ha) s hs
        · intro x hx s hs
          exact hsep x (chainGreedy_filter_subset hA hx) s hs
      rw [chainGreedy_eq_insert hAS, hmin, hfilter, hih, chainGreedy_eq_insert hA,
        Finset.insert_union]
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      rw [chainGreedy_empty, Finset.empty_union, Finset.empty_union]

theorem card_chainGreedy_union_of_sep {A S : Finset ℕ}
    (hlt : ∀ a ∈ A, ∀ s ∈ S, a < s)
    (hsep : ∀ x ∈ chainGreedy A, ∀ s ∈ S, x + 2 ≤ s) :
    (chainGreedy (A ∪ S)).card = (chainGreedy A).card + (chainGreedy S).card := by
  classical
  rw [chainGreedy_union_of_sep A S hlt hsep, Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.mpr ?_
  intro a ha hb
  exact absurd (hlt a (chainGreedy_subset A ha) a (chainGreedy_subset S hb)) (lt_irrefl a)

end GaloisForLFunctions.HTGeometry
