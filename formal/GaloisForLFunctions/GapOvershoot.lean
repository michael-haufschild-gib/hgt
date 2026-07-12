import Mathlib

/-!
# Gap overshoot bound

If a sum of monotone gap-sequence values `∑ᵢ bnat(nᵢ)` is smaller than `bnat(M+1)`, then every
index satisfies `nᵢ ≤ M` (`all_le_of_sum_bnat_lt`): a single term at index `≥ M+1` would already
exceed the whole sum.  This is the no-overshoot step underlying degree separation — at the
balanced index of a top-degree differential monomial, a lower-degree monomial cannot reach the
required source sum.
-/

open Finset

namespace GaloisForLFunctions

/-- **No overshoot.**  If `r` values of a monotone sequence sum to less than `bnat (M+1)`, each
index is at most `M`. -/
theorem all_le_of_sum_bnat_lt {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ} {n : Fin r → ℕ}
    {T M : ℕ} (hsum : ∑ i, bnat (n i) = T) (hT : T < bnat (M + 1)) : ∀ i, n i ≤ M := by
  intro i
  by_contra h
  push Not at h
  have h1 : bnat (M + 1) ≤ bnat (n i) := hmono h
  have h2 : bnat (n i) ≤ T := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun i => bnat (n i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  omega

/-- **Overshoot down.**  If `r` values of a monotone sequence, all with index `≤ M`, sum to more
than `(r-1)·bnat M + bnat (M-1)`, then every index equals `M`.  A single index below `M` drops
the sum by a full gap. -/
theorem all_eq_of_sum_bnat_gt {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ} {n : Fin r → ℕ}
    {T M : ℕ} (hsum : ∑ i, bnat (n i) = T) (hle : ∀ i, n i ≤ M)
    (hgt : (r - 1) * bnat M + bnat (M - 1) < T) : ∀ i, n i = M := by
  classical
  intro i
  by_contra h
  have hiM : n i ≤ M - 1 := by have := hle i; omega
  have hbi : bnat (n i) ≤ bnat (M - 1) := hmono hiM
  have hrest : ∑ j ∈ Finset.univ.erase i, bnat (n j) ≤ (r - 1) * bnat M := by
    have h1 : ∑ j ∈ Finset.univ.erase i, bnat (n j) ≤ (Finset.univ.erase i).card • bnat M :=
      Finset.sum_le_card_nsmul _ _ _ fun j _ => hmono (hle j)
    rwa [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
  have hsplit : bnat (n i) + ∑ j ∈ Finset.univ.erase i, bnat (n j) = T := by
    rw [← hsum]
    exact Finset.add_sum_erase Finset.univ (fun j => bnat (n j)) (Finset.mem_univ i)
  omega

end GaloisForLFunctions
