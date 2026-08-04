import GaloisForLFunctions.HTGeometry.FermionicFactorialTraceBound

/-!
# Harmonic capacity of a prime reservoir

Raw cardinality of a prime pool does not control the number of physical integers that can carry
many pool primes.  If every target contains at least `K` distinct members of `P`, double counting
its `K`-subsets bounds target cardinality by the level-`K` reciprocal weight.  The fermionic
factorial estimate then gives

`#targets ≤ B * (∑ p ∈ P, 1 / p)^K / K!`

whenever targets divisible by any fixed `K`-subset have cardinality at most
`B * ∏ p ∈ R, 1 / p`.  This is the finite physical-capacity gate for entropy-spread Route E
reservoirs.  It counts physical targets, not representation labels.
-/

namespace RHTower.Sieve

open Finset

/-- Reciprocal mass of a finite prime reservoir. -/
noncomputable def reciprocalPoolMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, 1 / (p : ℝ)

/-- Elementary-symmetric reciprocal weight of the `K`-th reservoir layer. -/
noncomputable def reciprocalLevelWeight (P : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ R ∈ P.powersetCard K, ∏ p ∈ R, 1 / (p : ℝ)

/-- Members of `P` which divide a physical integer. -/
def poolDivisors (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  P.filter fun p => p ∣ n

/-- Choosing `K` pool divisors is the same as choosing a `K`-subset of the pool all of whose
members divide the integer. -/
theorem powersetCard_poolDivisors (P : Finset ℕ) (n K : ℕ) :
    (poolDivisors P n).powersetCard K =
      (P.powersetCard K).filter (fun R => ∀ p ∈ R, p ∣ n) := by
  ext R
  simp only [Finset.mem_powersetCard, Finset.mem_filter, poolDivisors]
  constructor
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨?_, hcard⟩, ?_⟩
    · intro p hp
      exact (Finset.mem_filter.1 (hsub hp)).1
    · intro p hp
      exact (Finset.mem_filter.1 (hsub hp)).2
  · rintro ⟨⟨hsub, hcard⟩, hdvd⟩
    refine ⟨?_, hcard⟩
    intro p hp
    exact Finset.mem_filter.2 ⟨hsub hp, hdvd p hp⟩

/-- **Physical incidence lower bound.**  If every target contains at least `K` pool divisors,
then target cardinality is bounded by the sum, over `K`-subsets, of the corresponding physical
multiple counts. -/
theorem card_targets_le_sum_poolDivisorLevel
    (P targets : Finset ℕ) (K : ℕ)
    (hK : ∀ n ∈ targets, K ≤ (poolDivisors P n).card) :
    ((targets.card : ℕ) : ℝ) ≤
      ∑ R ∈ P.powersetCard K,
        (((targets.filter fun n => ∀ p ∈ R, p ∣ n).card : ℕ) : ℝ) := by
  calc
    ((targets.card : ℕ) : ℝ) = ∑ n ∈ targets, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ targets, (((poolDivisors P n).powersetCard K).card : ℝ) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hne : ((poolDivisors P n).powersetCard K).Nonempty :=
        Finset.powersetCard_nonempty.2 (hK n hn)
      exact_mod_cast Finset.card_pos.2 hne
    _ = ∑ n ∈ targets,
        ∑ R ∈ P.powersetCard K, if ∀ p ∈ R, p ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [powersetCard_poolDivisors, Finset.card_filter]
      push_cast
      rfl
    _ = ∑ R ∈ P.powersetCard K,
        ∑ n ∈ targets, if ∀ p ∈ R, p ∣ n then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ R ∈ P.powersetCard K,
        (((targets.filter fun n => ∀ p ∈ R, p ∣ n).card : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro R _
      rw [Finset.card_filter]
      push_cast
      rfl

/-- **Fermionic factorial bound for a reciprocal prime layer.** -/
theorem reciprocalLevelWeight_le (P : Finset ℕ) (K : ℕ) :
    reciprocalLevelWeight P K ≤
      reciprocalPoolMass P ^ K / ((K.factorial : ℕ) : ℝ) := by
  simpa [reciprocalLevelWeight, reciprocalPoolMass] using
    (GaloisForLFunctions.HTGeometry.sum_powersetCard_le_sum_pow_div_factorial
      (fun p : ℕ => div_nonneg zero_le_one (Nat.cast_nonneg p)) P K)

/-- **Harmonic terminal-capacity theorem.**  A physical `K`-subset multiple bound and reciprocal
pool mass bound the whole target set.  Representation multiplicity never appears. -/
theorem card_targets_le_reciprocalLevelWeight
    (P targets : Finset ℕ) (K : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ n ∈ targets, K ≤ (poolDivisors P n).card)
    (hmultiple : ∀ R ∈ P.powersetCard K,
      (((targets.filter fun n => ∀ p ∈ R, p ∣ n).card : ℕ) : ℝ) ≤
        B * ∏ p ∈ R, 1 / (p : ℝ)) :
    ((targets.card : ℕ) : ℝ) ≤
      B * (reciprocalPoolMass P ^ K / ((K.factorial : ℕ) : ℝ)) := by
  calc
    ((targets.card : ℕ) : ℝ) ≤
        ∑ R ∈ P.powersetCard K,
          (((targets.filter fun n => ∀ p ∈ R, p ∣ n).card : ℕ) : ℝ) :=
      card_targets_le_sum_poolDivisorLevel P targets K hK
    _ ≤ ∑ R ∈ P.powersetCard K, B * ∏ p ∈ R, 1 / (p : ℝ) :=
      Finset.sum_le_sum hmultiple
    _ = B * reciprocalLevelWeight P K := by
      rw [reciprocalLevelWeight, Finset.mul_sum]
    _ ≤ B * (reciprocalPoolMass P ^ K / ((K.factorial : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (reciprocalLevelWeight_le P K) hB

end RHTower.Sieve
