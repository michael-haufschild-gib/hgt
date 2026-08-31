import GaloisForLFunctions.HTGeometry.ChainGreedy

/-!
# The greedy scan skips the successor of what it just took

```text
chainGreedy_eq_insert         the defining unfolding
chainGreedy_insert_succ       ** x ∈ chainGreedy T ⟹ chainGreedy (insert (x+1) T) = chainGreedy T **
isChainFace_insert_succ       ** hence adjoining x+1 to a face keeps it a face **
```

The proof splits on whether `x` is the first greedy element: if it is, `x + 1` fails the filter and
disappears; if it is not, `x + 1` survives the filter and the induction hypothesis applies to the
smaller set.

This is the cone property the Cohen–Macaulay recursion needs.  In the recursion the forced set has
just taken `k`, and the least available vertex is `k + 1`; the lemma says that vertex can be
adjoined to every face, i.e. it is a cone point, so `isCohenMacaulayRing_of_isConePoint` and
`exists_isRegular_cone` apply and no shedding is required at that step.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower

theorem chainGreedy_eq_insert {T : Finset ℕ} (h : T.Nonempty) :
    chainGreedy T = insert (T.min' h) (chainGreedy (T.filter (fun y => T.min' h + 2 ≤ y))) := by
  conv_lhs => rw [chainGreedy]
  rw [dif_pos h]

/-- **Adjoining the successor of a greedy element changes nothing.**  The greedy scan, having just
taken `x`, skips `x + 1`. -/
theorem chainGreedy_insert_succ : ∀ (T : Finset ℕ) (x : ℕ), x ∈ chainGreedy T →
    chainGreedy (insert (x + 1) T) = chainGreedy T := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro x hx
    have hne : T.Nonempty := by
      rcases Finset.eq_empty_or_nonempty T with rfl | h
      · rw [chainGreedy_empty] at hx; simp at hx
      · exact h
    set m := T.min' hne with hm
    set T' := T.filter (fun y => m + 2 ≤ y) with hT'
    have hxT : x ∈ T := chainGreedy_subset T hx
    have hmx : m ≤ x := T.min'_le x hxT
    have hins : (insert (x + 1) T).Nonempty := ⟨x + 1, Finset.mem_insert_self _ _⟩
    have hminins : (insert (x + 1) T).min' hins = m := by
      refine le_antisymm ?_ ?_
      · exact Finset.min'_le _ m (Finset.mem_insert_of_mem (T.min'_mem hne))
      · refine Finset.le_min' _ _ _ ?_
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · exact T.min'_le y hy
    rw [chainGreedy_eq_insert hins, hminins, chainGreedy_eq_insert hne, ← hm, ← hT']
    congr 1
    rw [chainGreedy_eq_insert hne, ← hm, ← hT'] at hx
    rcases Finset.mem_insert.mp hx with hxm | hx'
    · -- x = m, so x + 1 = m + 1 is filtered out
      have : (insert (x + 1) T).filter (fun y => m + 2 ≤ y) = T' := by
        subst hxm
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert, hT']
        constructor
        · rintro ⟨hz | hz, hge⟩
          · omega
          · exact ⟨hz, hge⟩
        · rintro ⟨hz, hge⟩
          exact ⟨Or.inr hz, hge⟩
      rw [this]
    · -- x is a greedy element of T', so x ≥ m + 2 and x + 1 survives the filter
      have hxT' : x ∈ T' := chainGreedy_subset T' hx'
      have hxge : m + 2 ≤ x := (Finset.mem_filter.mp hxT').2
      have : (insert (x + 1) T).filter (fun y => m + 2 ≤ y) = insert (x + 1) T' := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert, hT']
        constructor
        · rintro ⟨hz | hz, hge⟩
          · exact Or.inl hz
          · exact Or.inr ⟨hz, hge⟩
        · rintro (rfl | ⟨hz, hge⟩)
          · exact ⟨Or.inl rfl, by omega⟩
          · exact ⟨Or.inr hz, hge⟩
      rw [this]
      exact ih T' (filter_ssubset hne) x hx'

/-- **The cone property of the chain complex.**  Adjoining the successor of a greedy element of
`S ∪ A` to `S` keeps it a face. -/
theorem isChainFace_insert_succ {N r : ℕ} {S A : Finset (Fin N)} {x : ℕ} {y : Fin N}
    (hxy : (y : ℕ) = x + 1) (hx : x ∈ chainGreedy ((S ∪ A).image Fin.val))
    (hface : IsChainFace N r (S ∪ A)) : IsChainFace N r (insert y S ∪ A) := by
  classical
  rw [isChainFace_iff_card_chainGreedy] at hface ⊢
  have hunion : insert y S ∪ A = insert y (S ∪ A) := Finset.insert_union y S A
  have himg : (insert y S ∪ A).image Fin.val = insert (x + 1) ((S ∪ A).image Fin.val) := by
    rw [hunion, Finset.image_insert, hxy]
  rw [himg, chainGreedy_insert_succ _ x hx]
  exact hface


end GaloisForLFunctions.HTGeometry
