import GaloisForLFunctions.HTGeometry.ChainGreedySucc

/-!
# The greedy scan of a left segment survives inside the union

```text
chainGreedy_subset_union_of_lt   A entirely left of S ⟹ chainGreedy A ⊆ chainGreedy (A ∪ S)
mem_chainGreedy_union_of_lt      in particular a greedy element of A stays one in A ∪ S
```

The induction is on `A`: the minimum of `A ∪ S` is the minimum of `A`, both filters split as a
union, and the filtered `A` is still left of the filtered `S`.

This is what connects the two halves of the recursion.  The forced set is left of the available
set, so the vertex the greedy last took inside the forced set is still a greedy element of any face
together with the forced set — which is the hypothesis of `isChainFace_insert_succ`, the cone
property of shape II.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The greedy scan of a left segment survives inside the union.**  If every element of `A`
precedes every element of `S`, the greedy selection of `A` is part of that of `A ∪ S`. -/
theorem chainGreedy_subset_union_of_lt : ∀ (A S : Finset ℕ),
    (∀ a ∈ A, ∀ s ∈ S, a < s) → chainGreedy A ⊆ chainGreedy (A ∪ S) := by
  classical
  intro A
  induction A using Finset.strongInduction with
  | _ A ih =>
    intro S hlt
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
      have hfilter : (A ∪ S).filter (fun y => m + 2 ≤ y)
          = A.filter (fun y => m + 2 ≤ y) ∪ S.filter (fun y => m + 2 ≤ y) := by
        rw [Finset.filter_union]
      rw [chainGreedy_eq_insert hA, chainGreedy_eq_insert hAS, hmin, ← hm, hfilter]
      refine Finset.insert_subset_insert _ ?_
      refine ih _ (filter_ssubset hA) _ ?_
      intro a ha s hs
      exact hlt a (Finset.mem_of_mem_filter a ha) s (Finset.mem_of_mem_filter s hs)
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      rw [chainGreedy_empty]
      exact Finset.empty_subset _

/-- **The last forced vertex is a greedy element.**  If `A` is left of `S` and `k ∈ chainGreedy A`,
then `k` is still a greedy element of the union. -/
theorem mem_chainGreedy_union_of_lt {A S : Finset ℕ} {k : ℕ}
    (hlt : ∀ a ∈ A, ∀ s ∈ S, a < s) (hk : k ∈ chainGreedy A) :
    k ∈ chainGreedy (A ∪ S) :=
  chainGreedy_subset_union_of_lt A S hlt hk

end GaloisForLFunctions.HTGeometry
