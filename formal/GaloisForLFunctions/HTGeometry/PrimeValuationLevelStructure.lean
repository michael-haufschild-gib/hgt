import GaloisForLFunctions.HTGeometry.PrimeValuationInfiniteSupport
import GaloisForLFunctions.HTGeometry.GeometricTailMass

/-!
# The level structure of a random valuation vector

The valuation at `p` reaches level `m` with probability exactly `p^{-m}`, so the hitting dichotomy
reads the level structure of the sector off the convergence of `∑_p p^{-m}`:

* at level one the series diverges, so almost every configuration is divisible by infinitely many
  primes;
* at every level `m ≥ 2` the series converges, so almost every configuration has only finitely many
  primes of multiplicity `m`.

Level one is therefore the exact threshold, and the two halves combine into a complete description of
a random valuation vector: almost surely it has infinitely many prime divisors, only finitely many of
them repeated, hence infinitely many simple ones.  A random integer is squarefree away from a finite
set of primes.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- **The local level mass.**  The valuation at `p` is at least `m` with probability `p^{-m}`. -/
theorem primeValuationLaw_Ici (p : Nat.Primes) (m : ℕ) :
    primeValuationLaw p {k : ℕ | m ≤ k} =
      ENNReal.ofReal ((((p : ℕ) : ℝ))⁻¹ ^ m) := by
  rw [primeValuationLaw, geometricMeasure_Ici (primeValuationParam_ne_zero p) m,
    primeValuationParam_coe]
  congr 1
  ring

/-- The level-two masses are summable, being the squares of the prime reciprocals. -/
theorem summable_primeReciprocal_sq :
    Summable fun p : Nat.Primes => (((p : ℕ) : ℝ))⁻¹ ^ 2 := by
  refine (Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).congr fun p => ?_
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hp.le,
    Real.rpow_natCast, ← inv_pow]

/-- **Above level one the local masses are summable.** -/
theorem tsum_primeValuationLaw_Ici_ne_top {m : ℕ} (hm : 2 ≤ m) :
    (∑' p : Nat.Primes, primeValuationLaw p {k : ℕ | m ≤ k}) ≠ ∞ := by
  rw [tsum_congr fun p => primeValuationLaw_Ici p m]
  rw [tsum_ofReal_ne_top_iff_summable _ fun p => by positivity]
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    summable_primeReciprocal_sq
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := one_lt_prime_cast p
  have hinv0 : (0 : ℝ) ≤ (((p : ℕ) : ℝ))⁻¹ := by positivity
  have hinv1 : (((p : ℕ) : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hp1.le
  exact pow_le_pow_of_le_one hinv0 hinv1 hm

/-- **Almost every configuration has only finitely many primes of multiplicity `m ≥ 2`.** -/
theorem primeValuationMeasure_finite_level {m : ℕ} (hm : 2 ≤ m) :
    primeValuationMeasure
        {k : ∀ _ : Nat.Primes, ℕ | {p : Nat.Primes | m ≤ k p}.Finite} = 1 := by
  rw [primeValuationMeasure]
  exact measure_finiteHit_eq_one primeValuationLaw (fun _ => {k : ℕ | m ≤ k})
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))
    (tsum_primeValuationLaw_Ici_ne_top hm)

theorem ae_finite_level {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ k ∂primeValuationMeasure, {p : Nat.Primes | m ≤ k p}.Finite := by
  rw [primeValuationMeasure]
  exact ae_finite_localHitSet primeValuationLaw (fun _ => {k : ℕ | m ≤ k})
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))
    (tsum_primeValuationLaw_Ici_ne_top hm)

/-- **Almost every configuration is squarefree away from a finite set of primes.** -/
theorem ae_finite_squarefull :
    ∀ᵐ k ∂primeValuationMeasure, {p : Nat.Primes | 2 ≤ k p}.Finite :=
  ae_finite_level le_rfl

/-- **The level structure of a random valuation vector.**  Almost surely infinitely many primes
divide, only finitely many divide to a higher power, and hence infinitely many divide exactly
once. -/
theorem ae_primeValuation_level_structure :
    ∀ᵐ k ∂primeValuationMeasure,
      {p : Nat.Primes | 2 ≤ k p}.Finite ∧ {p : Nat.Primes | k p = 1}.Infinite := by
  filter_upwards [ae_infinite_occupiedSet_primeValuation, ae_finite_squarefull]
    with k hinf hfin
  refine ⟨hfin, ?_⟩
  have hsub : (occupiedSet k) \ {p : Nat.Primes | 2 ≤ k p} ⊆
      {p : Nat.Primes | k p = 1} := by
    intro p hp
    have h1 : k p ≠ 0 := hp.1
    have h2 : ¬ (2 ≤ k p) := hp.2
    show k p = 1
    omega
  exact (hinf.sdiff hfin).mono hsub

/-- The simple part is infinite while the repeated part is finite, so the repeated part cannot
account for the divisors of a random configuration. -/
theorem ae_infinite_simple_primes :
    ∀ᵐ k ∂primeValuationMeasure, {p : Nat.Primes | k p = 1}.Infinite := by
  filter_upwards [ae_primeValuation_level_structure] with k hk
  exact hk.2

end GaloisForLFunctions.HTGeometry
