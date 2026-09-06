import GaloisForLFunctions.RHTower.LiouvilleSignedCofactorDilation
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# Divisor audit of the Liouville prime-counting-error pairing

The observable R(N)=sum(m<=N) lambda(m)(theta(N/m)-N/m) is exactly a pair of
weighted Liouville sums. Expand theta, reindex the finite product region, and apply
lambda(pm)=-lambda(m). The resulting prime-divisor logarithmic weight contains no
new independent counting-error input.

This diagnoses what the signed-alignment experiments measure. It does not prove a
half-power bound, imply that a change of representation is useless, or retire the
arithmetic RH route. No numerical observations are premises of these identities.
-/

open scoped BigOperators
namespace RHTower
noncomputable section

/-- Sum of logarithms of the distinct prime divisors, counted once each. -/
def liouvilleDistinctPrimeLogWeight (n : ℕ) : ℂ :=
  ∑ p ∈ n.divisors with p.Prime, (Real.log p : ℂ)

/-- Exact finite divisor collapse of the literal theta/cofactor pairing. -/
theorem liouville_theta_quotient_sum (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, liouvilleC m *
      (Chebyshev.theta ((N : ℝ)/m) : ℂ)) =
    -∑ n ∈ Finset.Icc 1 N, liouvilleC n * liouvilleDistinctPrimeLogWeight n := by
  classical
  let G : ℕ → ℕ → ℂ := fun d k =>
    liouvilleC d * (if k.Prime then (Real.log k : ℂ) else 0)
  have hexpand : (∑ m ∈ Finset.Icc 1 N, liouvilleC m *
      (Chebyshev.theta ((N : ℝ)/m) : ℂ)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N/d), G d k := by
    apply Finset.sum_congr rfl
    intro d hd
    have hi : Finset.Ioc 0 (N/d) = Finset.Icc 1 (N/d) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [Chebyshev.theta, Nat.floor_div_eq_div, hi, Finset.sum_filter]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hp : k.Prime <;> simp [G, hp]
  rw [hexpand, ← Sieve.sum_divisors_swap, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Nat.sum_divisorsAntidiagonal G, Nat.sum_divisorsAntidiagonal' G]
  unfold liouvilleDistinctPrimeLogWeight
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpd := Nat.mem_divisors.mp hp
  by_cases hprime : p.Prime
  · have hlp : liouvilleC p = -1 := by
      simpa using liouvilleC_prime_pow hprime 1
    have hm := liouvilleC_mul p (n/p)
    rw [Nat.mul_div_cancel' hpd.1, hlp] at hm
    have hl : liouvilleC (n/p) = -liouvilleC n := by
      linear_combination hm
    simp [G, hprime, hl]
  · simp [G, hprime]

/-- The actual counting-error observable is exactly two weighted Liouville sums. -/
theorem liouvillePrimeCountingError_eq_weighted_liouville (N : ℕ) :
    liouvillePrimeCountingError N =
      -(∑ n ∈ Finset.Icc 1 N, liouvilleC n * liouvilleDistinctPrimeLogWeight n) -
      (N : ℂ) * ∑ n ∈ Finset.Icc 1 N, liouvilleC n / (n : ℂ) := by
  unfold liouvillePrimeCountingError liouvilleCofactorSum
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [liouville_theta_quotient_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring
end
end RHTower
