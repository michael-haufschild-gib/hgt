import GaloisForLFunctions.HTGeometry.PrimeValuationSector
import GaloisForLFunctions.HTGeometry.ProductOccupancyDichotomy
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The prime-valuation sector is not carried by the integers

The sector is the Kolmogorov product of the local geometric laws, so the occupancy dichotomy applies
to it verbatim.  The local occupancy mass at `p` is exactly `1/p`, and `∑_p 1/p` diverges, so almost
every configuration is divisible by infinitely many primes.

Consequently the configurations with only finitely many prime divisors form a null set.  These are
exactly the valuation vectors of the natural numbers, so the sector — the probabilistic model of a
random integer — assigns the integers themselves probability zero.  A single configuration with
finite support is null for the same reason, which recovers the nullity of the all-zero valuation from
independence and the divergence of `∑_p 1/p` instead of from the sieve density telescope.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- **The local occupancy masses of the sector diverge**, because they are the prime
reciprocals. -/
theorem tsum_primeValuationLaw_compl_zero :
    (∑' p : Nat.Primes, primeValuationLaw p {0}ᶜ) = ∞ := by
  have hcoe : ∀ p : Nat.Primes, primeValuationLaw p {0}ᶜ =
      ((((((p : ℕ) : ℝ))⁻¹).toNNReal : NNReal) : ENNReal) := by
    intro p
    rw [primeValuationLaw_compl_zero]
    rfl
  rw [tsum_congr hcoe]
  refine ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr fun h => ?_
  refine Nat.Primes.not_summable_one_div (h.congr fun p => ?_)
  have hnn : (0 : ℝ) ≤ (((p : ℕ) : ℝ))⁻¹ := by
    have := one_lt_prime_cast p
    positivity
  rw [Real.coe_toNNReal _ hnn, one_div]

/-- **Almost every configuration is divisible by infinitely many primes.** -/
theorem primeValuationMeasure_infiniteSupport :
    primeValuationMeasure {k : ∀ _ : Nat.Primes, ℕ | (occupiedSet k).Infinite} = 1 := by
  rw [primeValuationMeasure]
  exact measure_infiniteOccupancy_eq_one primeValuationLaw
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))
    tsum_primeValuationLaw_compl_zero

theorem ae_infinite_occupiedSet_primeValuation :
    ∀ᵐ k ∂primeValuationMeasure, (occupiedSet k).Infinite := by
  rw [primeValuationMeasure]
  exact ae_infinite_occupiedSet primeValuationLaw
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))
    tsum_primeValuationLaw_compl_zero

/-- **Finitely many prime divisors is a null event.** -/
theorem primeValuationMeasure_finiteSupport :
    primeValuationMeasure {k : ∀ _ : Nat.Primes, ℕ | (occupiedSet k).Finite} = 0 := by
  rw [finiteOccupancy_eq_compl, primeValuationMeasure,
    MeasureTheory.prob_compl_eq_zero_iff (measurableSet_infiniteOccupancy
      (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes))))]
  exact measure_infiniteOccupancy_eq_one primeValuationLaw
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))
    tsum_primeValuationLaw_compl_zero

/-- **Every finitely supported configuration is null.**  The all-zero valuation is the
empty-support case. -/
theorem primeValuationMeasure_singleton_of_finite_occupiedSet
    {k : ∀ _ : Nat.Primes, ℕ} (hk : (occupiedSet k).Finite) :
    primeValuationMeasure {k} = 0 := by
  rw [primeValuationMeasure]
  exact measure_singleton_eq_zero_of_finite_occupiedSet primeValuationLaw
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))
    tsum_primeValuationLaw_compl_zero hk

/-! ## The arithmetic points -/

/-- The valuation vector of a natural number. -/
def natValuationVector (n : ℕ) : ∀ _ : Nat.Primes, ℕ :=
  fun p => n.factorization (p : ℕ)

theorem finite_occupiedSet_natValuationVector (n : ℕ) :
    (occupiedSet (natValuationVector n)).Finite := by
  have hfin : ((fun p : Nat.Primes => (p : ℕ)) ⁻¹'
      (↑n.factorization.support : Set ℕ)).Finite :=
    Set.Finite.preimage (Subtype.coe_injective.injOn)
      n.factorization.support.finite_toSet
  refine hfin.subset fun p hp => ?_
  have hp' : n.factorization (p : ℕ) ≠ 0 := hp
  show (p : ℕ) ∈ (↑n.factorization.support : Set ℕ)
  exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hp')

/-- **The integers are null in the sector.**  Every natural number has finitely many prime
divisors, so the arithmetic points carry no mass: the product model of a random integer is
supported away from the integers. -/
theorem primeValuationMeasure_range_natValuationVector :
    primeValuationMeasure (Set.range natValuationVector) = 0 := by
  refine MeasureTheory.measure_mono_null (fun k hk => ?_)
    primeValuationMeasure_finiteSupport
  obtain ⟨n, rfl⟩ := hk
  exact finite_occupiedSet_natValuationVector n

end GaloisForLFunctions.HTGeometry
