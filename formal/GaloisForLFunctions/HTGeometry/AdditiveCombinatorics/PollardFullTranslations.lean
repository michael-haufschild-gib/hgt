import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardDysonEnergy

/-!
# Bounding the set of full translations

`card_le_card_inter_add_holes` is the elementary fact that a single coset slice of a set `S` by a
subgroup `H` misses at most the total number of `H`-holes of `S`.

`card_dysonFull_add_card_le` uses it, together with Kneser applied to `dysonFull A B` and `B`, to
show that when every `H`-coset slice of `B` has fewer than `t` points — the condition
Grynkiewicz calls (qubal) — the set of translations carrying `B` inside `A` satisfies
`#T + #B + 1 ≤ #A + t`.  This is the upper bound for `#T` that feeds the energy estimate of
STEP 3.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
/-- A coset slice of `S` misses at most the total number of `H`-holes of `S`. -/
theorem card_le_card_inter_add_holes {S H : Finset G} {b : G} (hb : b ∈ S) :
    H.card ≤ ((b • H) ∩ S).card + ((S * H) \ S).card := by
  classical
  have hsub : (b • H) \ ((b • H) ∩ S) ⊆ (S * H) \ S := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_inter] at hz
    refine Finset.mem_sdiff.2 ⟨?_, fun hzS => hz.2 ⟨hz.1, hzS⟩⟩
    obtain ⟨h, hh, rfl⟩ := Finset.mem_smul_finset.1 hz.1
    exact mul_mem_mul hb hh
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left : (b • H) ∩ S ⊆ b • H)
  have h3 : (b • H).card = H.card := Finset.card_smul_finset _ _
  omega

/-- **The bound `#T ≤ #A − #B + t − 1`.**  If every coset slice of `B` by the stabiliser of
`T · B` has fewer than `t` points, then `T = dysonFull A B` cannot be large. -/
theorem card_dysonFull_add_card_le {A B : Finset G} (t : ℕ)
    (hTne : (dysonFull A B).Nonempty) (hB : B.Nonempty)
    (hqubal : ∀ b ∈ B,
      ((b • mulStab (dysonFull A B * B)) ∩ B).card + 1 ≤ t) :
    (dysonFull A B).card + B.card + 1 ≤ A.card + t := by
  classical
  by_contra hcon
  push Not at hcon
  set T := dysonFull A B with hTdef
  set H := mulStab (T * B) with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (T * B)
  have hTB : (T * B).card ≤ A.card := Finset.card_le_card (dysonFull_mul_subset A B)
  have hKn := card_mul_le_card_mul_mulStab T B hTne hB
  rw [← hHdef] at hKn
  have hhT := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul T)
  have hhB := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul B)
  obtain ⟨b, hb⟩ := hB
  have hslice := card_le_card_inter_add_holes (S := B) (H := H) hb
  have hq := hqubal b hb
  omega

end GaloisForLFunctions.HTGeometry.AddComb
