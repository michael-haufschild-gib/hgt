import GaloisForLFunctions.HTGeometry.OccupationSubsetPrimitivity
import GaloisForLFunctions.HTGeometry.SubsetPairTransitivity

/-!
# The occupation-state endgame without primitivity

The root action on the critical occupation states is the induced action of the ground-set symmetric
group on `m`-subsets:

```text
rootAction_eq_finsetPerm    the two actions agree
```

so the transitivity of the symmetric group on pairs of subsets with a given intersection size
replaces the block-system analysis entirely:

```text
criticalOccupation_eq_top_of_rootAction_of_johnson_swap
    ** the root action and one transposition of two states meeting in j points give everything **
criticalOccupation_eq_top_of_rootAction_of_swap_of_lt        the unbalanced case, m < n
criticalOccupation_eq_top_of_rootAction_of_swap_balanced     the balanced case, m = n
```

In the unbalanced case nothing at all is needed about the transposition beyond the two states being
distinct: `j < m` is automatic and `2m ≠ m+n` holds.  In the balanced case exactly one geometric
fact is consumed — the two swapped states meet, that is, they are not a complementary pair.  This is
strictly weaker than primitivity, which the balanced case never had: complement pairs are a genuine
block system there.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

theorem rootAction_eq_finsetPerm (m n : ℕ) (σ : Equiv.Perm (Fin (m + n))) :
    criticalOccupationRootAction m n σ = finsetPerm (α := Fin (m + n)) m σ := by
  classical
  refine Equiv.ext fun S => ?_
  refine Subtype.ext ?_
  simp only [criticalOccupationRootAction, MulAction.toPermHom_apply, finsetPerm,
    MulAction.toPerm_apply]
  rfl

theorem card_inter_lt_of_ne {α : Type*} [DecidableEq α] {S T : Finset α} {m : ℕ}
    (hS : S.card = m) (hT : T.card = m) (hne : S ≠ T) : (S ∩ T).card < m := by
  have hle : (S ∩ T).card ≤ m := by
    rw [← hS]
    exact Finset.card_le_card Finset.inter_subset_left
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have h1 : S ∩ T = S :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h2 : S ⊆ T := by rw [← h1]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le h2 (by omega))

/-- **The occupation-state endgame without primitivity.**  A group of permutations of the critical
occupation states that contains the whole root action and one transposition of two states meeting in
`j` points is the full symmetric group on the states. -/
theorem criticalOccupation_eq_top_of_rootAction_of_johnson_swap {m n j : ℕ}
    (hj : j < m) (hbig : 2 * m ≤ m + n) (hne : j ≠ 0 ∨ 2 * m ≠ m + n)
    {G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m n))}
    (hroot : ∀ σ : Equiv.Perm (Fin (m + n)), criticalOccupationRootAction m n σ ∈ G)
    {S₀ T₀ : criticalHorizonOccupationStates m n}
    (hj0 : (S₀.1 ∩ T₀.1).card = j) (h0 : Equiv.swap S₀ T₀ ∈ G) :
    G = ⊤ := by
  classical
  refine eq_top_of_induced_symmetric_and_johnson_swap (α := Fin (m + n)) hj ?_ ?_ ?_ hj0 h0
  · rwa [Fintype.card_fin]
  · rwa [Fintype.card_fin]
  · intro σ
    rw [← rootAction_eq_finsetPerm]
    exact hroot σ

/-- The unbalanced case needs nothing about the transposition beyond its existence. -/
theorem criticalOccupation_eq_top_of_rootAction_of_swap_of_lt {m n : ℕ}
    (_hm : 0 < m) (hlt : m < n)
    {G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m n))}
    (hroot : ∀ σ : Equiv.Perm (Fin (m + n)), criticalOccupationRootAction m n σ ∈ G)
    {S₀ T₀ : criticalHorizonOccupationStates m n} (hST : S₀ ≠ T₀)
    (h0 : Equiv.swap S₀ T₀ ∈ G) :
    G = ⊤ := by
  classical
  have hcard : (S₀.1 ∩ T₀.1).card < m :=
    card_inter_lt_of_ne S₀.2 T₀.2 (fun hc => hST (Subtype.ext hc))
  exact criticalOccupation_eq_top_of_rootAction_of_johnson_swap hcard (by omega)
    (Or.inr (by omega)) hroot rfl h0

/-- The balanced case needs exactly one thing: the transposition is not of a complementary pair. -/
theorem criticalOccupation_eq_top_of_rootAction_of_swap_balanced {m : ℕ}
    (_hm : 0 < m)
    {G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m m))}
    (hroot : ∀ σ : Equiv.Perm (Fin (m + m)), criticalOccupationRootAction m m σ ∈ G)
    {S₀ T₀ : criticalHorizonOccupationStates m m} (hST : S₀ ≠ T₀)
    (hmeet : (S₀.1 ∩ T₀.1).Nonempty)
    (h0 : Equiv.swap S₀ T₀ ∈ G) :
    G = ⊤ := by
  classical
  have hcard : (S₀.1 ∩ T₀.1).card < m :=
    card_inter_lt_of_ne S₀.2 T₀.2 (fun hc => hST (Subtype.ext hc))
  refine criticalOccupation_eq_top_of_rootAction_of_johnson_swap hcard (by omega)
    (Or.inl ?_) hroot rfl h0
  exact Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr hmeet)

end GaloisForLFunctions.HTGeometry
