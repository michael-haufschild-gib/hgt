import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring

/-!
# Distinct-prime signs and Möbius convolution

The sign `(-1)^ω(n)` counts distinct primes, so its value on every positive
prime power is `-1`. Möbius inversion identifies its squarefree source as
`μ(n) 2^ω(n)`. More generally, a prime weight `w` has squarefree source
`μ(n) ∏ p ∣ n, w(p)` and divisor sum `∏ p ∣ n, (1 - w(p))`.
This is the coefficient form of the rational Euler factors
`(1 - 2z)/(1 - z)`.
-/

noncomputable section

namespace GaloisForLFunctions.SelbergClass

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

variable {R : Type*} [CommRing R]

private theorem primeWeight_prime_pow (w : ℕ → R) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    prodPrimeFactors w (p ^ k) = w p := by
  rw [prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hk hp]
  exact Finset.prod_singleton _ _

private theorem squarefreeWeight_prime_pow (w : ℕ → R) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    ((moebius : ArithmeticFunction R).pmul (prodPrimeFactors w)) (p ^ k) =
      if k = 1 then -w p else 0 := by
  rw [pmul_apply, intCoe_apply, moebius_apply_prime_pow hp hk,
    primeWeight_prime_pow w hp hk]
  split_ifs <;> simp

/-- Möbius-weighted prime products have an exact divisor transform, including
integers with repeated prime factors. -/
theorem zeta_mul_squarefreePrimeWeight (w : ℕ → R) :
    (ζ : ArithmeticFunction R) *
        (moebius : ArithmeticFunction R).pmul (prodPrimeFactors w) =
      prodPrimeFactors (fun p => 1 - w p) := by
  have hmul := isMultiplicative_zeta.natCast.mul
    (isMultiplicative_moebius.intCast.pmul (IsMultiplicative.prodPrimeFactors w))
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    (IsMultiplicative.prodPrimeFactors (fun p => 1 - w p))).mpr
  intro p k hp
  cases k with
  | zero => simp [prodPrimeFactors_apply]
  | succ k =>
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp,
      primeWeight_prime_pow _ hp (Nat.succ_ne_zero _)]
    induction k with
    | zero =>
      simp [Finset.sum_range_succ, moebius_apply_prime hp,
        prodPrimeFactors_apply, hp.primeFactors, hp.ne_zero, sub_eq_add_neg]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih,
        squarefreeWeight_prime_pow w hp (Nat.succ_ne_zero _),
        if_neg (by omega), add_zero]

/-- The squarefree source is recovered by convolving with Möbius. -/
theorem moebius_mul_primeWeight_complement (w : ℕ → R) :
    (moebius : ArithmeticFunction R) * prodPrimeFactors (fun p => 1 - w p) =
      (moebius : ArithmeticFunction R).pmul (prodPrimeFactors w) := by
  rw [← zeta_mul_squarefreePrimeWeight, ← mul_assoc,
    coe_moebius_mul_coe_zeta, one_mul]

/-- The prime-product transform as a literal divisor sum. -/
theorem sum_divisors_squarefreePrimeWeight (w : ℕ → R) (n : ℕ) :
    (∑ d ∈ (n + 1).divisors, (moebius d : R) * ∏ p ∈ d.primeFactors, w p) =
      ∏ p ∈ (n + 1).primeFactors, (1 - w p) := by
  have h := congrArg (fun f : ArithmeticFunction R => f (n + 1))
    (zeta_mul_squarefreePrimeWeight w)
  rw [coe_zeta_mul_apply, prodPrimeFactors_apply (Nat.succ_ne_zero _)] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [pmul_apply, intCoe_apply,
    prodPrimeFactors_apply (Nat.pos_of_mem_divisors hd).ne']

/-- Distinct-prime sign, extended by zero at zero for Dirichlet convolution. -/
def distinctPrimeSign : ArithmeticFunction ℤ := prodPrimeFactors (fun _ => -1)

/-- The coefficient at every positive integer is `(-1)^ω(n)`. -/
theorem distinctPrimeSign_succ (n : ℕ) :
    distinctPrimeSign (n + 1) = (-1 : ℤ) ^ (n + 1).primeFactors.card := by
  simp [distinctPrimeSign, prodPrimeFactors_apply]

/-- Distinct-prime signs are multiplicative. -/
theorem distinctPrimeSign_isMultiplicative : distinctPrimeSign.IsMultiplicative :=
  IsMultiplicative.prodPrimeFactors _

/-- Möbius inversion produces the squarefree weights `μ(n) 2^ω(n)`. -/
theorem moebius_mul_distinctPrimeSign :
    moebius * distinctPrimeSign = moebius.pmul (prodPrimeFactors (fun _ => (2 : ℤ))) := by
  simpa [distinctPrimeSign] using
    moebius_mul_primeWeight_complement (fun _ => (2 : ℤ))

/-- An unconditional divisor formula for the arithmetic sign. -/
theorem distinctPrimeSign_divisor_sum (n : ℕ) :
    (∑ d ∈ (n + 1).divisors, moebius d * (2 : ℤ) ^ d.primeFactors.card) =
      (-1 : ℤ) ^ (n + 1).primeFactors.card := by
  simpa using sum_divisors_squarefreePrimeWeight (fun _ => (2 : ℤ)) n

#print axioms zeta_mul_squarefreePrimeWeight
#print axioms moebius_mul_distinctPrimeSign
#print axioms distinctPrimeSign_divisor_sum

end GaloisForLFunctions.SelbergClass
