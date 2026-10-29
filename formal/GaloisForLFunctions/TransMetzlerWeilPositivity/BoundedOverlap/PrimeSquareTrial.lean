import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions
import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeParityRamanujanCoordinates

/-!
# A prime-square truncation of the single-prime sign

The profile is negative exactly on integers of prime valuation one. It has
unit square and its correlation with multiplication by the prime differs
from minus one only on the prime-square fibre.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

/-- The sign that agrees with prime parity through valuation two. -/
def primeSquareTrial (p n : ℕ) : ℝ :=
  1 - 2 * (if p ∣ n then 1 else 0) + 2 * (if p ^ 2 ∣ n then 1 else 0)

private theorem dvd_of_square_dvd {p n : ℕ} (h : p ^ 2 ∣ n) : p ∣ n :=
  (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans h

/-- The truncated sign has exactly unit square at every integer. -/
theorem primeSquareTrial_sq (p n : ℕ) : primeSquareTrial p n ^ 2 = 1 := by
  unfold primeSquareTrial
  by_cases hp : p ∣ n
  · by_cases hp2 : p ^ 2 ∣ n <;> simp only [hp, hp2, if_true, if_false] <;> norm_num
  · have hp2 : ¬ p ^ 2 ∣ n := fun h => hp (dvd_of_square_dvd h)
    simp only [hp, hp2, if_false]
    norm_num

theorem abs_primeSquareTrial (p n : ℕ) : |primeSquareTrial p n| = 1 := by
  have h := primeSquareTrial_sq p n
  rcases sq_eq_one_iff.mp h with h | h <;> rw [h] <;> norm_num

/-- Multiplication by the prime shifts the exceptional fibre by one valuation. -/
theorem primeSquareTrial_mul {p : ℕ} (hp : 0 < p) (n : ℕ) :
    primeSquareTrial p (p * n) = -1 + 2 * (if p ∣ n then 1 else 0) := by
  have hpow : p ^ 2 ∣ p * n ↔ p ∣ n := by
    rw [pow_two]
    exact Nat.mul_dvd_mul_iff_left hp
  simp only [primeSquareTrial, dvd_mul_right, if_true, hpow]
  ring

/-- The first prime correlation cancels except on the prime-square fibre. -/
theorem primeSquareTrial_mul_correlation {p : ℕ} (hp : 0 < p) (n : ℕ) :
    primeSquareTrial p n * primeSquareTrial p (p * n) =
      -1 + 2 * (if p ^ 2 ∣ n then 1 else 0) := by
  rw [primeSquareTrial_mul hp, primeSquareTrial]
  by_cases hpn : p ∣ n
  · by_cases hp2 : p ^ 2 ∣ n <;> simp only [hpn, hp2, if_true, if_false] <;> norm_num
  · have hp2 : ¬ p ^ 2 ∣ n := fun h => hpn (dvd_of_square_dvd h)
    simp only [hpn, hp2, if_false]
    norm_num

/-- Products of two trial values have absolute value one, including all later prime powers. -/
theorem abs_primeSquareTrial_product (p m n : ℕ) :
    |primeSquareTrial p m * primeSquareTrial p n| = 1 := by
  rw [abs_mul, abs_primeSquareTrial, abs_primeSquareTrial, one_mul]

/-- Divisibility by a prime is the sum of its two Ramanujan conductors. -/
theorem ramanujan_prime_indicator {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    1 + ramanujanLagCoefficient p n =
      (p : ℝ) * (if p ∣ n then 1 else 0) := by
  have h := sum_divisors_ramanujanLagCoefficient hn hp.pos
  rw [hp.divisors] at h
  have h1 : ramanujanLagCoefficient 1 n = 1 := by
    simpa using (ramanujanLagCoefficient_of_dvd (one_dvd n))
  rw [sum_insert (show (1 : ℕ) ∉ ({p} : Finset ℕ) by
    simpa only [mem_singleton] using hp.ne_one.symm), sum_singleton, h1] at h
  simpa only [mul_ite, mul_one, mul_zero] using h

/-- At the prime square, the divisor sum contains exactly three conductors. -/
theorem ramanujan_primeSquare_indicator {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    1 + ramanujanLagCoefficient p n + ramanujanLagCoefficient (p ^ 2) n =
      (p : ℝ) ^ 2 * (if p ^ 2 ∣ n then 1 else 0) := by
  have h := sum_divisors_ramanujanLagCoefficient hn (pow_pos hp.pos 2)
  rw [Nat.divisors_prime_pow hp, sum_map] at h
  change (∑ j ∈ range 3, ramanujanLagCoefficient (p ^ j) n) =
    (if p ^ 2 ∣ n then ((p ^ 2 : ℕ) : ℝ) else 0) at h
  have h1 : ramanujanLagCoefficient 1 n = 1 := by
    simpa using (ramanujanLagCoefficient_of_dvd (one_dvd n))
  norm_num [Finset.sum_range_succ, h1] at h
  simpa only [mul_ite, mul_one, mul_zero] using h

/-- The trial has an explicit expansion supported on `1`, `p`, and `p²`. -/
theorem primeSquareTrial_ramanujan {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    primeSquareTrial p n =
      (1 - 2 / (p : ℝ) + 2 / (p : ℝ) ^ 2) * ramanujanLagCoefficient 1 n +
      (-2 / (p : ℝ) + 2 / (p : ℝ) ^ 2) * ramanujanLagCoefficient p n +
      (2 / (p : ℝ) ^ 2) * ramanujanLagCoefficient (p ^ 2) n := by
  have h1 : ramanujanLagCoefficient 1 n = 1 := by
    simpa using (ramanujanLagCoefficient_of_dvd (one_dvd n))
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hprime := ramanujan_prime_indicator hp hn
  have hsquare := ramanujan_primeSquare_indicator hp hn
  rw [h1, mul_one, primeSquareTrial]
  field_simp
  linear_combination 2 * (p : ℝ) * hprime - 2 * hsquare

open SelectiveMultiscaleArithmeticPositivity ArithmeticCountingPositivity

/-- Harmonic mass of a divisibility fibre is a decimated harmonic sum. -/
theorem harmonic_indicator {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) / n) =
      (1 / (d : ℝ)) * gaugeHarmonicSum (fun _ => 1) (N / d) := by
  have h := gaugeHarmonicSum_multiples (fun _ => 1) euler_matching.1 hd N
  rw [sum_filter] at h
  simpa only [ite_div, zero_div, one_div] using h

/-- The first prime correlation has an exact finite-horizon harmonic formula. -/
theorem primeSquareTrial_harmonic_correlation {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ n ∈ Icc 1 N, primeSquareTrial p n * primeSquareTrial p (p * n) / n) =
      -gaugeHarmonicSum (fun _ => 1) N +
        (2 / (p : ℝ) ^ 2) * gaugeHarmonicSum (fun _ => 1) (N / p ^ 2) := by
  simp_rw [primeSquareTrial_mul_correlation hp, add_div, mul_div_assoc]
  rw [sum_add_distrib, ← mul_sum, harmonic_indicator (pow_pos hp 2)]
  simp only [gaugeHarmonicSum, neg_div, sum_neg_distrib, Nat.cast_pow]
  ring

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.primeSquareTrial_mul_correlation
