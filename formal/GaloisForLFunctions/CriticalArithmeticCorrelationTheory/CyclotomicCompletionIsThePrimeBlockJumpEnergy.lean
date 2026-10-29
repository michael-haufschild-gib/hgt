import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AllDivisorConductorsRecoverTheDiscreteBridge
import GaloisForLFunctions.BezoutValuationIncidence.BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo

/-!
# Cyclotomic completion equals the prime-block jump energy

The conductor-completed overlap Gram and the cumulative prime-block jump
form are two exact realizations of the same discrete bridge kernel. This
identity transfers the full mixed form, rather than only its diagonal.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence

/-- Completing primitive conductors is exactly the pronic energy of the
cumulative prime jumps, multiplied by the period. -/
theorem completedCyclotomicGram_eq_primePacketJumpEnergy
    (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) {Q : ℕ} (hQ : 0 < Q)
    (hS : ∀ p ∈ S, (p : ℕ) < Q) :
    (∑ m ∈ Q.divisors.erase 1, ∑ p ∈ S, ∑ q ∈ S,
      a p * a q * primitivePrefixGram m p q) =
      (Q : ℝ) * ∑ n ∈ range Q,
        primePacketJumpSum S a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [sum_range_primePacketJumpSum_sq_div S a hS]
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  calc
    _ = ∑ p ∈ S, ∑ m ∈ Q.divisors.erase 1, ∑ q ∈ S,
        a p * a q * primitivePrefixGram m p q := sum_comm
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ m ∈ Q.divisors.erase 1,
        a p * a q * primitivePrefixGram m p q :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ p ∈ S, ∑ q ∈ S, a p * a q *
        ((Q : ℝ) * min (p : ℕ) (q : ℕ) - (p : ℕ) * (q : ℕ)) := by
      refine sum_congr rfl fun p hp => sum_congr rfl fun q hq => ?_
      rw [← mul_sum, sum_nontrivial_divisors_primitivePrefixGram hQ
        (hS p hp).le (hS q hq).le]
    _ = _ := by
      rw [mul_sum]
      refine sum_congr rfl fun p _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun q _ => ?_
      rw [Nat.cast_min]
      field_simp
      <;> ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.completedCyclotomicGram_eq_primePacketJumpEnergy
