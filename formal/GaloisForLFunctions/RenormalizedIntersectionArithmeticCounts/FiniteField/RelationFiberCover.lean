import Mathlib.SetTheory.Cardinal.Finite

/-!
# Upper bounds from fiber covers

When a relation is covered by a family of constant-cardinality fibers
and a section, their total cardinality bounds its solution set above.
No injectivity is needed for this direction.
-/

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- Covering every solution by one of the fibers or the section gives the complementary upper bound. -/
theorem card_relation_upper_bound_add_section
    {I J Y Z : Type*} [Finite I] [Finite J] [Finite Y] [Finite Z]
    (P : Y → Z → Prop) (f : I → Y) (g : J → Y)
    (z : J → Z) (hz : ∀ j, P (g j) (z j))
    (hcover : ∀ y w, P y w → (∃ i, f i = y) ∨ ∃ j, g j = y ∧ z j = w)
    (n : ℕ) (hn : ∀ i, Nat.card {w : Z | P (f i) w} = n) :
    Nat.card {t : Y × Z // P t.1 t.2} ≤ Nat.card I * n + Nat.card J := by
  classical
  letI := Fintype.ofFinite I
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite Z
  let F : (Σ i : I, {w : Z | P (f i) w}) ⊕ J → {t : Y × Z // P t.1 t.2} :=
    Sum.elim (fun x => ⟨(f x.1, x.2.val), x.2.property⟩) (fun j => ⟨(g j, z j), hz j⟩)
  have hF : Function.Surjective F := by
    rintro ⟨⟨y, w⟩, hyw⟩
    rcases hcover y w hyw with ⟨i, hi⟩ | ⟨j, hj, hzj⟩
    · refine ⟨Sum.inl ⟨i, w, ?_⟩, ?_⟩
      · change P (f i) w
        simpa only [hi] using hyw
      · apply Subtype.ext
        change (f i, w) = (y, w)
        rw [hi]
    · refine ⟨Sum.inr j, ?_⟩
      apply Subtype.ext
      change (g j, z j) = (y, w)
      rw [hj, hzj]
  have hc := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_sum, Nat.card_sigma, Finset.sum_const_nat (fun i _ => hn i),
    Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
  exact hc

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
