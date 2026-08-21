import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.RepresentationCount

/-!
# Critical pairs and the Dyson transform

Two ingredients of Pollard-type theorems for `t`-representable sums.

* `card_mul_lt_of_insert`: a *critical pair* — one with `#(A · B) = #A + #B − 1` and aperiodic
  product set — cannot have its second factor enlarged without enlarging the product set.
* `dysonLarge`/`dysonSmall`: the Dyson transform `(A, B) ↦ ((x • B) ∪ A, (x • B) ∩ A)`.  It
  preserves the sum of the cardinalities (`card_dysonLarge_add_card_dysonSmall`) and cannot
  increase representation counts (`rep_dyson_le`), hence maps `i`-representable products into a
  translate of the original ones (`repSet_dyson_subset`).
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **Critical pairs are maximal.**  If `#(A · B) = #A + #B − 1` and `A · B` has trivial
stabiliser, then enlarging `B` by any new element strictly enlarges the product set. -/
theorem card_mul_lt_of_insert {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hcard : (A * B).card + 1 = A.card + B.card)
    (haper : mulStab (A * B) = {1}) {b : G} (hb : b ∉ B) :
    (A * B).card < (A * (insert b B)).card := by
  classical
  have hsub : A * B ⊆ A * insert b B := mul_subset_mul_left (Finset.subset_insert b B)
  rcases lt_or_eq_of_le (Finset.card_le_card hsub) with h | h
  · exact h
  · exfalso
    have heq : A * B = A * insert b B := Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
    have hBcard : (insert b B).card = B.card + 1 := Finset.card_insert_of_notMem hb
    have hkn := card_add_card_le_card_mul_add_card_mulStab A (insert b B) hA
      (hB.mono (Finset.subset_insert b B))
    rw [← heq, haper, Finset.card_singleton, hBcard] at hkn
    omega

/-! ### The Dyson transform -/

/-- The Dyson transform of `(A, B)` at `x`: the smaller set `(x • B) ∩ A`. -/
def dysonSmall (A B : Finset G) (x : G) : Finset G := (x • B) ∩ A

/-- The Dyson transform of `(A, B)` at `x`: the larger set `(x • B) ∪ A`. -/
def dysonLarge (A B : Finset G) (x : G) : Finset G := (x • B) ∪ A

omit [Fintype G] in
theorem card_dysonLarge_add_card_dysonSmall (A B : Finset G) (x : G) :
    (dysonLarge A B x).card + (dysonSmall A B x).card = A.card + B.card := by
  rw [dysonLarge, dysonSmall, Finset.card_union_add_card_inter, Finset.card_smul_finset]
  omega

omit [Fintype G] in
/-- The Dyson transform does not increase representation counts, after translating by `x`. -/
theorem rep_dyson_le (A B : Finset G) (x g : G) :
    rep (dysonLarge A B x) (dysonSmall A B x) g ≤ rep A B (x⁻¹ * g) := by
  classical
  have hkey : ∀ w : G, w ∈ x • B → x⁻¹ * w ∈ B := by
    intro w hw
    obtain ⟨b, hbB, hbw⟩ := mem_smul_finset.1 hw
    simp only [smul_eq_mul] at hbw
    rw [← hbw, inv_mul_cancel_left]
    exact hbB
  simp only [rep]
  refine Finset.card_le_card_of_injOn
    (fun p => if p.1 ∈ A then (p.1, x⁻¹ * p.2) else (p.2, x⁻¹ * p.1)) ?_ ?_
  · rintro ⟨u, v⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, dysonLarge, dysonSmall,
      Finset.mem_union, Finset.mem_inter] at hp
    obtain ⟨⟨hu, hvxB, hvA⟩, huv⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    by_cases huA : u ∈ A
    · rw [if_pos huA]
      exact ⟨⟨huA, hkey v hvxB⟩, by rw [← huv]; exact mul_left_comm u x⁻¹ v⟩
    · rw [if_neg huA]
      have hux : u ∈ x • B := hu.resolve_right huA
      refine ⟨⟨hvA, hkey u hux⟩, ?_⟩
      rw [← huv, mul_left_comm, mul_comm v u]
  · rintro ⟨u, v⟩ hp ⟨u', v'⟩ hp' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, dysonSmall,
      Finset.mem_inter] at hp hp'
    have hvA : v ∈ A := hp.1.2.2
    have hv'A : v' ∈ A := hp'.1.2.2
    simp only at heq
    split_ifs at heq with h1 h2 h2
    · rw [Prod.mk.injEq] at heq
      have e2 : v = v' := mul_left_cancel heq.2
      rw [Prod.mk.injEq]
      exact ⟨heq.1, e2⟩
    · rw [Prod.mk.injEq] at heq
      have e2 : v = u' := mul_left_cancel heq.2
      exact absurd (e2 ▸ hvA) h2
    · rw [Prod.mk.injEq] at heq
      have e2 : u = v' := mul_left_cancel heq.2
      exact absurd (e2 ▸ hv'A) h1
    · rw [Prod.mk.injEq] at heq
      have e2 : u = u' := mul_left_cancel heq.2
      rw [Prod.mk.injEq]
      exact ⟨e2, heq.1⟩

theorem repSet_dyson_subset (A B : Finset G) (x : G) (i : ℕ) :
    repSet (dysonLarge A B x) (dysonSmall A B x) i ⊆ x • repSet A B i := by
  intro g hg
  rw [mem_repSet] at hg
  have h := rep_dyson_le A B x g
  rw [mem_smul_finset]
  refine ⟨x⁻¹ * g, ?_, by simp⟩
  rw [mem_repSet]
  omega

end GaloisForLFunctions.HTGeometry.AddComb
