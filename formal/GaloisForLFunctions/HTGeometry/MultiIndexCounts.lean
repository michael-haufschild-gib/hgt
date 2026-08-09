import Mathlib

/-!
# Multi-index counts for a dimension comparison

The two elementary bounds that turn "too many coefficients for too few conditions" into an
inequality between explicit powers.

* **`card_le_pow_of_sum_lt`** — a family of multi-indices in `n` variables of total degree below
  `N` has at most `N ^ n` members, since each coordinate is then below `N`;
* **`pow_le_card_of_box_subset`** — a family containing the whole box `{β : ∀ i, β i ≤ m}` in `k`
  variables has at least `(m + 1) ^ k` members.

Applied with `k = n + 1` to the coefficient space of polynomials of degree at most `(n+1)·m` and
with `N` to the space of Taylor jets of order below `N`, these give the comparison the Siegel
count needs.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **Multi-indices of small total degree are few.** -/
theorem card_le_pow_of_sum_lt {n N : ℕ} (s : Finset (Fin n → ℕ))
    (hs : ∀ β ∈ s, ∑ i, β i < N) : s.card ≤ N ^ n := by
  classical
  have hsub : s ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range N) := by
    intro β hβ
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.single_le_sum (f := fun j => β j)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) (hs β hβ)
  calc s.card ≤ (Fintype.piFinset (fun _ : Fin n => Finset.range N)).card :=
        Finset.card_le_card hsub
    _ = N ^ n := by simp

/-- **A family containing a box is large.** -/
theorem pow_le_card_of_box_subset {k m : ℕ} (s : Finset (Fin k → ℕ))
    (hs : ∀ β : Fin k → ℕ, (∀ i, β i ≤ m) → β ∈ s) : (m + 1) ^ k ≤ s.card := by
  classical
  have hsub : Fintype.piFinset (fun _ : Fin k => Finset.range (m + 1)) ⊆ s := by
    intro β hβ
    rw [Fintype.mem_piFinset] at hβ
    exact hs β fun i => Nat.lt_succ_iff.mp (Finset.mem_range.mp (hβ i))
  calc (m + 1) ^ k
      = (Fintype.piFinset (fun _ : Fin k => Finset.range (m + 1))).card := by simp
    _ ≤ s.card := Finset.card_le_card hsub

end GaloisForLFunctions.HTGeometry
