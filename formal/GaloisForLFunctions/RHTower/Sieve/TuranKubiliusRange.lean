import GaloisForLFunctions.RHTower.Sieve.TuranKubilius
import GaloisForLFunctions.RHTower.Sieve.RamareWeight

/-!
# Turán–Kubilius for a range of primes

The short-interval argument designates the primes of a *range* `(z₀, z]`, not an initial segment,
and weights an integer by how many of them divide it.  The variance of that count is the difference
of two initial-segment counts, so it follows from the initial-segment variance at both ends with a
factor two.

The designated set is `Nat.primesLE z \ Nat.primesLE z₀`, whose count at `n` is exactly the corpus's
`primeFactorsIn`, and whose harmonic mass is `mertensS z − mertensS z₀`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The primes of a range, as the designated set of a Ramaré/Turán–Kubilius weight. -/
def primesRange (z₀ z : ℕ) : Finset ℕ := Nat.primesLE z \ Nat.primesLE z₀

theorem mem_primesLE {z p : ℕ} : p ∈ Nat.primesLE z ↔ p ≤ z ∧ p.Prime := by
  rw [Nat.primesLE, Nat.mem_primesBelow]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem primesLE_subset {z₀ z : ℕ} (h : z₀ ≤ z) : Nat.primesLE z₀ ⊆ Nat.primesLE z := by
  intro p hp
  rw [mem_primesLE] at hp ⊢
  exact ⟨by omega, hp.2⟩

theorem primesRange_prime {z₀ z p : ℕ} (hp : p ∈ primesRange z₀ z) : p.Prime := by
  rw [primesRange, Finset.mem_sdiff, mem_primesLE] at hp
  exact hp.1.2

/-- The designated count of a range is the difference of the two initial-segment counts. -/
theorem card_primeFactorsIn_primesRange {z₀ z : ℕ} (hz : z₀ ≤ z) (n : ℕ) :
    ((primeFactorsIn (primesRange z₀ z) n).card : ℝ)
      = (omegaCount z n : ℝ) - (omegaCount z₀ n : ℝ) := by
  classical
  have hsub : {p ∈ Nat.primesLE z₀ | p ∣ n} ⊆ {p ∈ Nat.primesLE z | p ∣ n} := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨primesLE_subset hz hp.1, hp.2⟩
  have hset : primeFactorsIn (primesRange z₀ z) n
      = {p ∈ Nat.primesLE z | p ∣ n} \ {p ∈ Nat.primesLE z₀ | p ∣ n} := by
    ext p
    simp only [primeFactorsIn, primesRange, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hset, Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
  rw [omegaCount, omegaCount, Nat.cast_sub (Finset.card_le_card hsub)]

/-- The harmonic mass of a range of primes. -/
theorem sum_inv_primesRange {z₀ z : ℕ} (hz : z₀ ≤ z) :
    ∑ p ∈ primesRange z₀ z, 1 / (p : ℝ) = mertensS z - mertensS z₀ := by
  rw [primesRange, Finset.sum_sdiff_eq_sub (primesLE_subset hz), mertensS, mertensS]

/-- **Turán–Kubilius for a range of primes.**  The variance of the designated count over an interval
of integers is at most twice the variance at each end. -/
theorem sum_variance_primesRange_le {z₀ z : ℕ} (hz : z₀ ≤ z) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b,
        (((primeFactorsIn (primesRange z₀ z) n).card : ℝ) - (mertensS z - mertensS z₀)) ^ 2
      ≤ 4 * ((b : ℝ) - a) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
        + 8 * ((Nat.primesLE z).card : ℝ) ^ 2 := by
  classical
  have hpi : ((Nat.primesLE z₀).card : ℝ) ≤ ((Nat.primesLE z).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (primesLE_subset hz)
  have hpi0 : (0 : ℝ) ≤ ((Nat.primesLE z₀).card : ℝ) := Nat.cast_nonneg _
  have hmert : mertensS z₀ ≤ mertensS z := by
    rw [mertensS, mertensS]
    refine Finset.sum_le_sum_of_subset_of_nonneg (primesLE_subset hz) fun p hp _ => ?_
    have hp0 : 0 < p := by
      rw [mem_primesLE] at hp
      exact hp.2.pos
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    positivity
  have hab0 : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hterm : ∀ n ∈ Finset.Ioc a b,
      (((primeFactorsIn (primesRange z₀ z) n).card : ℝ) - (mertensS z - mertensS z₀)) ^ 2
        ≤ 2 * ((omegaCount z n : ℝ) - mertensS z) ^ 2
          + 2 * ((omegaCount z₀ n : ℝ) - mertensS z₀) ^ 2 := by
    intro n _
    rw [card_primeFactorsIn_primesRange hz n]
    nlinarith [sq_nonneg (((omegaCount z n : ℝ) - mertensS z)
      + ((omegaCount z₀ n : ℝ) - mertensS z₀)),
      sq_nonneg (((omegaCount z n : ℝ) - mertensS z) - ((omegaCount z₀ n : ℝ) - mertensS z₀))]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := sum_omegaCount_variance_le z a b hab
  have h2 := sum_omegaCount_variance_le z₀ a b hab
  have hmono : ((b : ℝ) - a) * mertensS z₀ ≤ ((b : ℝ) - a) * mertensS z :=
    mul_le_mul_of_nonneg_left hmert hab0
  nlinarith [h1, h2, hmono, hpi, hpi0]

end

end RHTower.Sieve
