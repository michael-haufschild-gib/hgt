import GaloisForLFunctions.RHTower.Sieve.PrimePairPaperScale
import GaloisForLFunctions.RHTower.Sieve.PrimePairDivisorWeightedMean

/-!
# Divisor-weighted same-block collisions at the paper scale

This file combines the distinct-pair and repeated-prime pieces of the Matomäki--Teräväinen
`c₃,n` support into one inclusive prime fibre.  Its reciprocal mass is at most `3δ_A`; the
divisor-weighted pair mean then gives the exact paper-scale collision estimate while retaining the
outer prime reciprocal mass.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Inclusive same-block fibre: the outer prime itself plus larger primes in its short block. -/
def primeCollisionFibre (b : ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  insert p (primesIco (p + 1) (b p))

/-- The outer prime does not occur in its strict upper fibre. -/
theorem prime_not_mem_strictCollisionFibre (b : ℕ → ℕ) (p : ℕ) :
    p ∉ primesIco (p + 1) (b p) := by
  intro hp
  have := (mem_primesIco.mp hp).1
  omega

/-- The inclusive pair count is exactly the distinct-or-repeated block collision count. -/
theorem primePairDivisorCount_collisionFibre_eq
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    primePairDivisorCount S (primeCollisionFibre b) n = primeBlockCollisionCount S b n := by
  simp only [primePairDivisorCount, primeCollisionFibre, primeBlockCollisionCount,
    primeSquareDivisorCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_insert (prime_not_mem_strictCollisionFibre b p)]
  ring

/-- Every inclusive collision fibre has reciprocal mass at most `3δ_A`. -/
theorem eventually_sum_inv_primeCollisionFibre_le_three_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℕ) (b : ℕ → ℕ),
      (∀ p ∈ S, mtLowerCutoff X ≤ (p : ℝ)) →
      (∀ p ∈ S, p + 1 ≤ b p) →
      (∀ p ∈ S, ((b p - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * (p : ℝ)) →
      ∀ p ∈ S, ∑ q ∈ primeCollisionFibre b p, 1 / (q : ℝ) ≤
        3 * mtPaperWidth A X := by
  filter_upwards [eventually_sum_inv_primesIco_le_two_paperWidth A,
    eventually_recip_le_paperWidth_of_mtLowerCutoff_le A] with X hmassX hrecipX
  intro S b hlower hle hband p hp
  have hpSub : p + 1 - 1 = p := by omega
  have hstrict : ∑ q ∈ primesIco (p + 1) (b p), 1 / (q : ℝ) ≤
      2 * mtPaperWidth A X := by
    simpa only [hpSub] using
      hmassX (a := p + 1) (b := b p) (hlower p hp) (hle p hp) (hband p hp)
  have hdiag := hrecipX (hlower p hp)
  rw [primeCollisionFibre, Finset.sum_insert (prime_not_mem_strictCollisionFibre b p)]
  nlinarith

/-- Divisor-weighted count of distinct or repeated same-block prime collisions. -/
def weightedPrimeBlockCollisionCount
    (K : ℕ) (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ K * primeBlockCollisionCount S b n

/-- Paper-scale weighted collision estimate, retaining the decisive outer reciprocal mass. -/
theorem eventually_sum_weightedPrimeBlockCollisionCount_paperWidth (A K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℕ) (b : ℕ → ℕ) (Y : ℕ),
      1 ≤ Y →
      (∀ p ∈ S, p.Prime) →
      (∀ p ∈ S, mtLowerCutoff X ≤ (p : ℝ)) →
      (∀ p ∈ S, p + 1 ≤ b p) →
      (∀ p ∈ S, ((b p - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * (p : ℝ)) →
      ∑ n ∈ Finset.Icc 1 Y, weightedPrimeBlockCollisionCount K S b n ≤
        (4 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
          (3 * mtPaperWidth A X) * ∑ p ∈ S, 1 / (p : ℝ) := by
  filter_upwards [eventually_sum_inv_primeCollisionFibre_le_three_paperWidth A]
    with X hmassX
  intro S b Y hY hprime hlower hle hband
  have hT : ∀ p ∈ S, ∀ q ∈ primeCollisionFibre b p, q.Prime := by
    intro p hp q hq
    rcases Finset.mem_insert.mp hq with hqp | hq
    · subst q
      exact hprime p hp
    · exact (mem_primesIco.mp hq).2.2
  have h := sum_weightedPrimePairDivisorCount_le_of_fibreMass
    K Y hY S (primeCollisionFibre b) hprime hT (hmassX S b hlower hle hband)
  rw [show (∑ n ∈ Finset.Icc 1 Y, weightedPrimeBlockCollisionCount K S b n) =
      ∑ n ∈ Finset.Icc 1 Y,
        weightedPrimePairDivisorCount K S (primeCollisionFibre b) n by
    apply Finset.sum_congr rfl
    intro n hn
    unfold weightedPrimeBlockCollisionCount weightedPrimePairDivisorCount
    rw [primePairDivisorCount_collisionFibre_eq]]
  exact h

end

end RHTower.Sieve
