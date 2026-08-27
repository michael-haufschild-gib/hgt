import GaloisForLFunctions.RHTower.Sieve.RamarePhaseError

/-!
# Prime-pair divisor means

The `c₃,n` error in Matomäki--Teräväinen, Lemma 2.3, is supported on integers carrying two prime
factors in one short multiplicative block.  This file gives the exact factorial-moment counting
engine: a prescribed family of ordered prime pairs contributes according to divisibility by the
product, hence has mean bounded by its double reciprocal mass.  Equal-prime pairs are counted by
the separate square-divisor term.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Real-valued count of prescribed ordered pairs whose product divides `n`. -/
def primePairDivisorCount (S : Finset ℕ) (T : ℕ → Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ T p, if p * q ∣ n then 1 else 0

/-- A divisibility indicator sums to the exact count of multiples. -/
theorem sum_dvdIndicator_Icc (Y d : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, (if d ∣ n then (1 : ℝ) else 0) = ((Y / d : ℕ) : ℝ) := by
  rw [← card_Icc_filter_dvd Y d]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [Finset.sum_filter]

/-- Mean pair count bounded by the exact double reciprocal mass. -/
theorem sum_primePairDivisorCount_le
    (S : Finset ℕ) (T : ℕ → Finset ℕ) (Y : ℕ)
    (hS : ∀ p ∈ S, 0 < p) (hT : ∀ p ∈ S, ∀ q ∈ T p, 0 < q) :
    ∑ n ∈ Finset.Icc 1 Y, primePairDivisorCount S T n ≤
      (Y : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) * ∑ q ∈ T p, 1 / (q : ℝ) := by
  calc
    ∑ n ∈ Finset.Icc 1 Y, primePairDivisorCount S T n =
        ∑ p ∈ S, ∑ q ∈ T p,
          ∑ n ∈ Finset.Icc 1 Y, (if p * q ∣ n then (1 : ℝ) else 0) := by
      unfold primePairDivisorCount
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ S, ∑ q ∈ T p, ((Y / (p * q) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact sum_dvdIndicator_Icc Y (p * q)
    _ ≤ ∑ p ∈ S, ∑ q ∈ T p, (Y : ℝ) / ((p : ℝ) * (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hcast : ((Y / (p * q) : ℕ) : ℝ) ≤ (Y : ℝ) / ((p * q : ℕ) : ℝ) :=
        Nat.cast_div_le
      push_cast at hcast
      exact hcast
    _ = (Y : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) * ∑ q ∈ T p, 1 / (q : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hS p hp
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hT p hp q hq
      field_simp

/-- Uniform fibre mass factors out of the double reciprocal sum. -/
theorem sum_primePairDivisorCount_le_of_fibreMass
    (S : Finset ℕ) (T : ℕ → Finset ℕ) (Y : ℕ)
    (hS : ∀ p ∈ S, 0 < p) (hT : ∀ p ∈ S, ∀ q ∈ T p, 0 < q)
    {η : ℝ} (hmass : ∀ p ∈ S, ∑ q ∈ T p, 1 / (q : ℝ) ≤ η) :
    ∑ n ∈ Finset.Icc 1 Y, primePairDivisorCount S T n ≤
      (Y : ℝ) * η * ∑ p ∈ S, 1 / (p : ℝ) := by
  calc
    ∑ n ∈ Finset.Icc 1 Y, primePairDivisorCount S T n ≤
        (Y : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) * ∑ q ∈ T p, 1 / (q : ℝ) :=
      sum_primePairDivisorCount_le S T Y hS hT
    _ ≤ (Y : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) * η := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Y)
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hmass p hp)
        (one_div_nonneg.mpr (by exact_mod_cast (hS p hp).le))
    _ = (Y : ℝ) * η * ∑ p ∈ S, 1 / (p : ℝ) := by
      rw [← Finset.sum_mul]
      ring

/-- Count of primes in `S` whose square divides `n`. -/
def primeSquareDivisorCount (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, if p * p ∣ n then 1 else 0

/-- Mean square-divisor count bounded by the diagonal reciprocal mass. -/
theorem sum_primeSquareDivisorCount_le
    (S : Finset ℕ) (Y : ℕ) (hS : ∀ p ∈ S, 0 < p) :
    ∑ n ∈ Finset.Icc 1 Y, primeSquareDivisorCount S n ≤
      (Y : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) ^ 2 := by
  calc
    ∑ n ∈ Finset.Icc 1 Y, primeSquareDivisorCount S n =
        ∑ p ∈ S, ∑ n ∈ Finset.Icc 1 Y,
          (if p * p ∣ n then (1 : ℝ) else 0) := by
      unfold primeSquareDivisorCount
      rw [Finset.sum_comm]
    _ = ∑ p ∈ S, ((Y / (p * p) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sum_dvdIndicator_Icc Y (p * p)
    _ ≤ ∑ p ∈ S, (Y : ℝ) / ((p : ℝ) * (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hcast : ((Y / (p * p) : ℕ) : ℝ) ≤ (Y : ℝ) / ((p * p : ℕ) : ℝ) :=
        Nat.cast_div_le
      push_cast at hcast
      exact hcast
    _ = (Y : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hS p hp
      field_simp

/-- If every reciprocal in `S` is at most `η`, the diagonal has the same linear-mass shape. -/
theorem sum_primeSquareDivisorCount_le_of_recip
    (S : Finset ℕ) (Y : ℕ) (hS : ∀ p ∈ S, 0 < p) {η : ℝ}
    (hrecip : ∀ p ∈ S, 1 / (p : ℝ) ≤ η) :
    ∑ n ∈ Finset.Icc 1 Y, primeSquareDivisorCount S n ≤
      (Y : ℝ) * η * ∑ p ∈ S, 1 / (p : ℝ) := by
  calc
    ∑ n ∈ Finset.Icc 1 Y, primeSquareDivisorCount S n ≤
        (Y : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) ^ 2 :=
      sum_primeSquareDivisorCount_le S Y hS
    _ ≤ (Y : ℝ) * ∑ p ∈ S, η * (1 / (p : ℝ)) := by
      gcongr with p hp
      have hnonneg : 0 ≤ 1 / (p : ℝ) :=
        one_div_nonneg.mpr (by exact_mod_cast (hS p hp).le)
      nlinarith [hrecip p hp]
    _ = (Y : ℝ) * η * ∑ p ∈ S, 1 / (p : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end

end RHTower.Sieve
