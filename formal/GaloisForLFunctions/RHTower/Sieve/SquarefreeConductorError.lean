import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientDivisorIdentity
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The squarefree conductor factor in mollifier errors

Each local factor `p(p+1)/(p-1)^2` is at most six. Multiplication gives
the conductor bound used in Lemma 9 of Gonçalves–Kerr–Klurman–Vedana,
*The Riemann zeta function at the zeros of real-rooted trigonometric polynomials*.
The squarefree reciprocal-totient weight extends the bound to every integer.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

private theorem prime_local_conductor_bound {p : ℕ} (hp : p.Prime) :
    (p : ℝ) * ((p : ℝ) + 1) ≤ 6 * ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  nlinarith only [sq_nonneg ((p : ℝ) - 2), hp2]

private theorem squarefree_conductor_bound {q : ℕ} (hq : Squarefree q) :
    (q : ℝ) * (sigma 1 q : ℝ) ≤
      6 ^ q.primeFactors.card * (q.totient : ℝ) ^ 2 := by
  have hqprod : (∏ p ∈ q.primeFactors, (p : ℝ)) = q := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]
  have hsigprod : (∏ p ∈ q.primeFactors, (sigma 1 p : ℝ)) = sigma 1 q := by
    exact_mod_cast (isMultiplicative_sigma (k := 1)).prod_primeFactors hq
  have hphiNat : q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree hq, Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero),
      one_mul]
  have hphi : (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [hphiNat, Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  have hsigma {p : ℕ} (hp : p.Prime) : (sigma 1 p : ℝ) = (p : ℝ) + 1 := by
    have h := sigma_one_apply_prime_pow (i := 1) hp
    simpa [Finset.sum_range_succ, add_comm] using congrArg (fun m : ℕ => (m : ℝ)) h
  calc
    (q : ℝ) * (sigma 1 q : ℝ) =
        ∏ p ∈ q.primeFactors, (p : ℝ) * ((p : ℝ) + 1) := by
      rw [← hqprod, ← hsigprod, ← prod_mul_distrib]
      exact prod_congr rfl fun p hp => by rw [hsigma (Nat.prime_of_mem_primeFactors hp)]
    _ ≤ ∏ p ∈ q.primeFactors, 6 * ((p : ℝ) - 1) ^ 2 :=
      prod_le_prod (fun p _ => by positivity)
        (fun _ hp => prime_local_conductor_bound (Nat.prime_of_mem_primeFactors hp))
    _ = 6 ^ q.primeFactors.card * (q.totient : ℝ) ^ 2 := by
      rw [prod_mul_distrib, prod_const, prod_pow, ← hphi]

/-- The squarefree mollifier's conductor error is controlled by its number of prime factors. -/
theorem sqfreeTotientInv_conductor_error_le (q : ℕ) :
    (q : ℝ) * (∑ d ∈ q.divisors, (d : ℝ)) * (sqfreeTotientInv q) ^ 2 ≤
      6 ^ q.primeFactors.card := by
  by_cases hq : Squarefree q
  · have hphi : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq.ne_zero)
    have hsum : (∑ d ∈ q.divisors, (d : ℝ)) = (sigma 1 q : ℝ) := by
      rw [sigma_one_apply, Nat.cast_sum]
    rw [sqfreeTotientInv_apply, if_pos hq, hsum, div_pow, one_pow, one_div, ← div_eq_mul_inv]
    exact (div_le_iff₀ (sq_pos_of_pos hphi)).mpr (squarefree_conductor_bound hq)
  · rw [sqfreeTotientInv_apply, if_neg hq]
    simp only [zero_pow (by omega : 2 ≠ 0), mul_zero]
    positivity

#print axioms sqfreeTotientInv_conductor_error_le

end RHTower.Sieve
