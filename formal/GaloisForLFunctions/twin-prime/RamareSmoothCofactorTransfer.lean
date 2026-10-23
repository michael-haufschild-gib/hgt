import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistRate
import GaloisForLFunctions.RHTower.Sieve.DampedCofactorIntegral
import GaloisForLFunctions.RHTower.Sieve.DampedLocalFactor
import GaloisForLFunctions.RHTower.Sieve.DampedCorrectionMassBudget
import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeReciprocalTail
import GaloisForLFunctions.RHTower.DampedMobiusSumsZeroFree

/-!
# Uniform Ramaré cofactor cancellation through smooth divisors

The prime-count damping is a convolution of the signed Möbius row with a
positive smooth-divisor kernel. The signed prefix estimate pays the small
divisors; a separate fractional moment pays the large divisors.
-/

namespace TwinPrime

open Finset ArithmeticFunction RHTower RHTower.Sieve
open Filter Topology

noncomputable section

/-- Retain the activity `u` on designated primes and activity one elsewhere. -/
def ramarePrimeActivity (P : Finset ℕ) (u : ℝ) (p : ℕ) : ℝ :=
  if p ∈ P then u else 1

/-- The nonnegative divisor kernel whose Möbius convolution gives prime-count damping. -/
def ramareSmoothKernel (P : Finset ℕ) (u : ℝ) : ArithmeticFunction ℝ :=
  DampedMobius.divisorSum (ramarePrimeActivity P u)

private theorem dampedOmegaMoebius_eq_real_dampedMobius {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (u : ℝ) (n : ℕ) :
    dampedOmegaMoebius P u n =
      (DampedMobius.dampedMobius (ramarePrimeActivity P u) n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [dampedOmegaMoebius, moebius_zero, Int.cast_zero, zero_mul,
      ArithmeticFunction.map_zero, Complex.ofReal_zero]
  have hset : primeFactorsIn P n = n.primeFactors.filter (· ∈ P) := by
    ext p
    simp only [mem_primeFactorsIn, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨⟨hP p hp, hd, hn⟩, hp⟩
    · rintro ⟨⟨_, hd, _⟩, hp⟩
      exact ⟨hp, hd⟩
  have hprod : (∏ p ∈ n.primeFactors, ramarePrimeActivity P u p) =
      u ^ (primeFactorsIn P n).card := by
    rw [hset, ← Finset.prod_const]
    exact (Finset.prod_filter (fun p => p ∈ P) (fun _ => u) n.primeFactors).symm
  rw [dampedOmegaMoebius, DampedMobius.dampedMobius, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.prodPrimeFactors_apply hn,
    hprod, Complex.ofReal_mul, Complex.ofReal_intCast]

private theorem ramareSmoothKernel_nonneg {P : Finset ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) : 0 ≤ ramareSmoothKernel P u n := by
  apply DampedMobius.divisorSum_nonneg
  intro p _
  unfold ramarePrimeActivity
  split_ifs
  · rwa [abs_of_nonneg hu0]
  · norm_num

private theorem ramareSmoothKernel_le_one {P : Finset ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) : ramareSmoothKernel P u n ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero]; norm_num
  rw [ramareSmoothKernel, DampedMobius.divisorSum,
    ArithmeticFunction.prodPrimeFactors_apply hn]
  apply Finset.prod_le_one
  · intro p _
    unfold ramarePrimeActivity
    split_ifs <;> linarith
  · intro p _
    unfold ramarePrimeActivity
    split_ifs <;> linarith

end

end TwinPrime

#print axioms RHTower.Sieve.exists_norm_sum_moebiusTwist_le_rate
