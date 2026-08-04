import GaloisForLFunctions.RHTower.Sieve.NoncoprimeUnionBound

/-!
# Splitting a prime range at a cut-off

The union bound runs over all primes up to `2√x`; the card's step 3 splits that range at a fixed
`P`, keeping the small primes for the sector densities `(9)` and sending the large ones to the tail
estimate `(11)`.  The split is exact:

    primesLE Q  =  primesLE P  ∪  bigPrimeSet P Q      (disjointly, for P ≤ Q),

so any sum over the full range is the sum of the two pieces.
-/

namespace RHTower.Sieve

open Finset

/-- The two prime ranges are disjoint. -/
theorem disjoint_primesLE_bigPrimeSet (P Q : ℕ) :
    Disjoint (Nat.primesLE P) (bigPrimeSet P Q) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [Nat.mem_primesLE] at hp
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hq
  omega

/-- **The prime range splits at the cut-off.** -/
theorem primesLE_eq_union {P Q : ℕ} (hPQ : P ≤ Q) :
    Nat.primesLE Q = Nat.primesLE P ∪ bigPrimeSet P Q := by
  ext p
  rw [Finset.mem_union, Nat.mem_primesLE, Nat.mem_primesLE, bigPrimeSet, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    rcases le_or_gt p P with h | h
    · exact Or.inl ⟨h, hp⟩
    · exact Or.inr ⟨⟨by omega, hle⟩, hp⟩
  · rintro (⟨hle, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
    · exact ⟨by omega, hp⟩
    · exact ⟨h2, hp⟩

/-- **A sum over a prime range splits at the cut-off.** -/
theorem sum_primesLE_split {P Q : ℕ} (hPQ : P ≤ Q) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE Q, f p
      = ∑ p ∈ Nat.primesLE P, f p + ∑ p ∈ bigPrimeSet P Q, f p := by
  rw [primesLE_eq_union hPQ, Finset.sum_union (disjoint_primesLE_bigPrimeSet P Q)]

/-- **The union bound, split at the cut-off.**  Card equations `(10)` and `(11)` combined. -/
theorem noncoprimePairCount_le_split {x h : ℝ} (hx : 0 < x) {P : ℕ}
    (hPQ : P ≤ ⌊2 * Real.sqrt x⌋₊) :
    noncoprimePairCount x h
      ≤ ∑ p ∈ Nat.primesLE P, sharedSectorCount x h p
        + ∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x h p := by
  rw [← sum_primesLE_split hPQ]
  exact noncoprimePairCount_le hx

end RHTower.Sieve
