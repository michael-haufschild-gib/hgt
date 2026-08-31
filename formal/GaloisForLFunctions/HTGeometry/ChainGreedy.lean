import GaloisForLFunctions.HTGeometry.ChainInterval

/-!
# The greedy scan computes the chain number

The largest `2`-separated subset of a finite set of naturals is produced by the greedy
left-to-right scan: take the least element, discard everything within distance one of it, repeat.

```text
chainGreedy T                    the greedy selection
chainGreedy_subset               it is a subset
chainGreedy_pairwise             ** it is 2-separated **
card_chainGreedy_insert          its size counts one per round
card_le_card_chainGreedy         ** it is optimal: every 2-separated subset is no larger **
isChainFace_iff_card_chainGreedy
    ** S is a face of Δ_r exactly when its greedy selection has at most r elements **
```

Optimality is the classical activity-selection argument, in its cleanest recursive form: a
`2`-separated subset has at most one element in `{m, m+1}` where `m` is the least element of the
ambient set, and the rest is a `2`-separated subset of what survives the filter — so it is at most
`1 +` the greedy count of that, which is the greedy count of the whole.

This is the lemma the remaining Cohen–Macaulay recursion for the Hankel card rests on: it is what
makes the star of a shed vertex a cone (the greedy, having just taken `k`, skips `k+1`), and it
gives the additivity of the chain number across a left/right split.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower

/-- The greedy left-to-right selection of a `2`-separated subset: repeatedly take the least
remaining element and discard everything within distance one of it. -/
noncomputable def chainGreedy (T : Finset ℕ) : Finset ℕ :=
  if h : T.Nonempty then
    insert (T.min' h) (chainGreedy (T.filter (fun x => T.min' h + 2 ≤ x)))
  else ∅
termination_by T.card
decreasing_by
  · have hmem : T.min' h ∈ T := T.min'_mem h
    have hnot : T.min' h ∉ T.filter (fun x => T.min' h + 2 ≤ x) := by
      simp only [Finset.mem_filter]
      omega
    have hsub : T.filter (fun x => T.min' h + 2 ≤ x) ⊆ T := Finset.filter_subset _ _
    exact Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr ⟨_, hmem, hnot⟩)

theorem chainGreedy_empty : chainGreedy ∅ = ∅ := by
  rw [chainGreedy]
  simp

theorem chainGreedy_subset (T : Finset ℕ) : chainGreedy T ⊆ T := by
  classical
  induction T using Finset.strongInduction with
  | _ T ih =>
    rw [chainGreedy]
    split
    · rename_i h
      refine Finset.insert_subset (T.min'_mem h) ?_
      refine (ih _ ?_).trans (Finset.filter_subset _ _)
      have hmem : T.min' h ∈ T := T.min'_mem h
      have hnot : T.min' h ∉ T.filter (fun x => T.min' h + 2 ≤ x) := by
        simp only [Finset.mem_filter]
        omega
      exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨_, hmem, hnot⟩
    · exact Finset.empty_subset _

theorem filter_ssubset {T : Finset ℕ} (h : T.Nonempty) :
    T.filter (fun x => T.min' h + 2 ≤ x) ⊂ T := by
  classical
  have hmem : T.min' h ∈ T := T.min'_mem h
  have hnot : T.min' h ∉ T.filter (fun x => T.min' h + 2 ≤ x) := by
    simp only [Finset.mem_filter]
    omega
  exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨_, hmem, hnot⟩

theorem chainGreedy_ge {T : Finset ℕ} (h : T.Nonempty) {x : ℕ}
    (hx : x ∈ chainGreedy (T.filter (fun y => T.min' h + 2 ≤ y))) : T.min' h + 2 ≤ x :=
  (Finset.mem_filter.mp (chainGreedy_subset _ hx)).2

/-- **The greedy selection is `2`-separated.** -/
theorem chainGreedy_pairwise (T : Finset ℕ) :
    (↑(chainGreedy T) : Set ℕ).Pairwise hankelChainGraph.Adj := by
  classical
  induction T using Finset.strongInduction with
  | _ T ih =>
    rw [chainGreedy]
    split
    · rename_i h
      intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact Or.inl (by have := chainGreedy_ge h hb; omega)
      · rcases hb with rfl | hb
        · exact Or.inr (by have := chainGreedy_ge h ha; omega)
        · exact ih _ (filter_ssubset h) ha hb hab
    · simp

theorem card_chainGreedy_insert {T : Finset ℕ} (h : T.Nonempty) :
    (chainGreedy T).card
      = (chainGreedy (T.filter (fun y => T.min' h + 2 ≤ y))).card + 1 := by
  classical
  conv_lhs => rw [chainGreedy]
  rw [dif_pos h, Finset.card_insert_of_notMem]
  intro hcon
  have := chainGreedy_ge h hcon
  omega

/-- **The greedy selection is optimal**: every `2`-separated subset is at most as large.  This is
the classical activity-selection argument: at most one element of the subset lies in `{m, m+1}`, and
the rest is a `2`-separated subset of the filtered set. -/
theorem card_le_card_chainGreedy : ∀ (T J : Finset ℕ), J ⊆ T →
    (↑J : Set ℕ).Pairwise hankelChainGraph.Adj → J.card ≤ (chainGreedy T).card := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro J hJT hJ
    by_cases h : T.Nonempty
    · set m := T.min' h with hm
      set J' := J.filter (fun x => m + 2 ≤ x) with hJ'
      have hsmall : (J.filter (fun x => ¬ (m + 2 ≤ x))).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [Finset.mem_filter] at ha hb
        by_contra hne
        have hadj := hJ (by simpa using ha.1) (by simpa using hb.1) hne
        have hma : m ≤ a := T.min'_le a (hJT ha.1)
        have hmb : m ≤ b := T.min'_le b (hJT hb.1)
        change a + 1 < b ∨ b + 1 < a at hadj
        omega
      have hsplit : J.card = J'.card + (J.filter (fun x => ¬ (m + 2 ≤ x))).card := by
        rw [hJ', Finset.card_filter_add_card_filter_not]
      have hJ'T : J' ⊆ T.filter (fun x => m + 2 ≤ x) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hJT hx.1, hx.2⟩
      have hJ'sub : J' ⊆ J := Finset.filter_subset _ _
      have hJ'pair : (↑J' : Set ℕ).Pairwise hankelChainGraph.Adj :=
        hJ.mono (by exact_mod_cast hJ'sub)
      have hrec := ih _ (filter_ssubset h) J' hJ'T hJ'pair
      rw [card_chainGreedy_insert h]
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      rw [Finset.subset_empty] at hJT
      simp [hJT]


/-- **`γ` is the greedy count**, in the form the chain complex uses: a set is a face of `Δ_r`
exactly when its greedy selection has at most `r` elements. -/
theorem isChainFace_iff_card_chainGreedy {N r : ℕ} (S : Finset (Fin N)) :
    IsChainFace N r S ↔ (chainGreedy (S.image Fin.val)).card ≤ r := by
  classical
  constructor
  · intro hface
    by_contra hcon
    push Not at hcon
    obtain ⟨J, hJsub, hJcard⟩ :=
      Finset.exists_subset_card_eq (show r + 1 ≤ (chainGreedy (S.image Fin.val)).card by omega)
    exact hface ⟨J, hJcard,
      (chainGreedy_pairwise _).mono (by exact_mod_cast hJsub),
      hJsub.trans (chainGreedy_subset _)⟩
  · rintro hle ⟨J, hcard, hpair, hsub⟩
    have := card_le_card_chainGreedy (S.image Fin.val) J hsub hpair
    omega

end GaloisForLFunctions.HTGeometry

