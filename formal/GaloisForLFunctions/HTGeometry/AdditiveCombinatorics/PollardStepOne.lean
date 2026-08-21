import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardGrynkiewicz

/-!
# The counting step of Grynkiewicz's STEP 1

When `A' · B'` is exactly the set of `t`-representable products of `A` and `B`, every element of
`A' · B'` contributes the full `t` to `repSum A B t`, and every *mixed* representation — one with
exactly one factor outside `A'` resp. `B'` — whose product falls outside `A' · B'` contributes an
extra `1`.  `repSum_ge_of_repSet_eq` records this.

The hypothesis `defect A A' B B' ≤ t` is what makes the mixed contributions cumulative: it bounds
the number of mixed representations of any single element by `t`, so none of them is lost to the
truncation `min(·, t)`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
theorem rep_le_card_left (A B : Finset G) (c : G) : rep A B c ≤ A.card := by
  rw [rep_eq_card_inter]
  exact Finset.card_le_card Finset.inter_subset_left

omit [Fintype G] in
/-- The mixed representation counts add up inside the total count. -/
theorem rep_sdiff_add_rep_sdiff_le {A A' B B' : Finset G} (hA' : A' ⊆ A) (hB' : B' ⊆ B) (c : G) :
    rep (A \ A') B' c + rep A' (B \ B') c ≤ rep A B c := by
  classical
  have hdisj : Disjoint (((A \ A') ×ˢ B').filter (fun p => p.1 * p.2 = c))
      ((A' ×ˢ (B \ B')).filter (fun p => p.1 * p.2 = c)) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff] at h1
    rw [Finset.mem_filter, Finset.mem_product] at h2
    exact h1.1.1.2 h2.1.1
  have hsub : (((A \ A') ×ˢ B').filter (fun p => p.1 * p.2 = c))
      ∪ ((A' ×ˢ (B \ B')).filter (fun p => p.1 * p.2 = c))
      ⊆ ((A ×ˢ B).filter (fun p => p.1 * p.2 = c)) := by
    intro p hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp <;>
      rw [Finset.mem_filter, Finset.mem_product] at hp ⊢ <;>
      refine ⟨⟨?_, ?_⟩, hp.2⟩
    · exact (Finset.mem_sdiff.1 hp.1.1).1
    · exact hB' hp.1.2
    · exact hA' hp.1.1
    · exact (Finset.mem_sdiff.1 hp.1.2).1
  rw [rep, rep, rep, ← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hsub


/-- **The counting form of Grynkiewicz's STEP 1.**  When `A' · B'` is exactly the set of
`t`-representable products, `repSum` dominates `t·#(A'·B')` plus every mixed representation whose
product falls outside `A'·B'`. -/
theorem repSum_ge_of_repSet_eq (A B A' B' : Finset G) (t : ℕ)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B) (heq : A' * B' = repSet A B t)
    (hl : defect A A' B B' ≤ t) :
    t * (A' * B').card
      + ∑ c ∈ Finset.univ \ (A' * B'), (rep (A \ A') B' c + rep A' (B \ B') c)
      ≤ repSum A B t := by
  classical
  rw [repSum_eq_sum_min]
  have hsplit : ∑ c ∈ Finset.univ \ (A' * B'), min (rep A B c) t
      + ∑ c ∈ A' * B', min (rep A B c) t = ∑ c : G, min (rep A B c) t :=
    Finset.sum_sdiff (Finset.subset_univ (A' * B'))
  have hin : ∑ c ∈ A' * B', min (rep A B c) t = t * (A' * B').card := by
    have hval : ∀ c ∈ A' * B', min (rep A B c) t = t := by
      intro c hc
      rw [heq, mem_repSet] at hc
      exact min_eq_right hc
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, mul_comm]
  have hout : ∑ c ∈ Finset.univ \ (A' * B'), (rep (A \ A') B' c + rep A' (B \ B') c)
      ≤ ∑ c ∈ Finset.univ \ (A' * B'), min (rep A B c) t := by
    refine Finset.sum_le_sum (fun c _ => ?_)
    have h1 : rep (A \ A') B' c + rep A' (B \ B') c ≤ rep A B c :=
      rep_sdiff_add_rep_sdiff_le hA' hB' c
    have h2 : rep (A \ A') B' c + rep A' (B \ B') c ≤ t := by
      have hL := rep_le_card_left (A \ A') B' c
      have hR := rep_le_card_right A' (B \ B') c
      rw [defect] at hl
      omega
    exact le_min h1 h2
  omega

end GaloisForLFunctions.HTGeometry.AddComb
