import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

/-!
# Matching inside a cell

A cardinality comparison inside a single cell yields a literal injection: if the sources are no more
numerous than the targets, there is a map sending each source to a distinct target of the same cell.

`#s ≤ #t → ∃ f, Set.InjOn f s ∧ ∀ x ∈ s, f x ∈ t`

This is the step that converts the counting statement — targets outnumber source primes in every
window — into the transport map the Hall statement asserts.  No structure beyond cardinality is used,
so the matching is available cell by cell and the cells may then be combined when they are disjoint.
-/

namespace RHTower.Sieve

open Finset

/-- **Matching inside a cell.** -/
theorem exists_injOn_of_card_le {s t : Finset ℕ} (h : s.card ≤ t.card) :
    ∃ f : ℕ → ℕ, Set.InjOn f ↑s ∧ ∀ x ∈ s, f x ∈ t := by
  classical
  obtain ⟨t', ht'sub, ht'card⟩ := Finset.exists_subset_card_eq h
  have hcard : s.card = t'.card := ht'card.symm
  let e := Finset.equivOfCardEq hcard
  refine ⟨fun x => if hx : x ∈ s then ((e ⟨x, hx⟩ : {y // y ∈ t'}) : ℕ) else 0, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only at hab
    rw [dif_pos ha, dif_pos hb] at hab
    have : (e ⟨a, ha⟩) = (e ⟨b, hb⟩) := Subtype.ext hab
    have := e.injective this
    exact Subtype.ext_iff.mp this
  · intro x hx
    simp only
    rw [dif_pos hx]
    exact ht'sub (e ⟨x, hx⟩).2

/-- **Matching with bounded displacement.**  Sources and targets in a common window of length `H`
are matched by an injection moving nothing further than `H`. -/
theorem exists_injOn_displacement_le {s t : Finset ℕ} {X H : ℕ} (h : s.card ≤ t.card)
    (hs : ∀ x ∈ s, X < x ∧ x ≤ X + H) (ht : ∀ y ∈ t, X < y ∧ y ≤ X + H) :
    ∃ f : ℕ → ℕ, Set.InjOn f ↑s ∧ (∀ x ∈ s, f x ∈ t)
      ∧ ∀ x ∈ s, |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  obtain ⟨f, hinj, hmem⟩ := exists_injOn_of_card_le h
  refine ⟨f, hinj, hmem, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hs x hx
  obtain ⟨hf1, hf2⟩ := ht (f x) (hmem x hx)
  rw [abs_le]
  constructor <;> omega

end RHTower.Sieve
