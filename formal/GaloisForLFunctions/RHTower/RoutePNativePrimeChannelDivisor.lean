import GaloisForLFunctions.RHTower.RoutePNativeSignedPairComparison

/-! # Literal divisor identity for every native prime-subset channel -/

open Finset

namespace RHTower.RoutePWindow

private theorem subset_moebius (S : Finset Nat.Primes) :
    ((ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) : ℤ) : ℝ) =
      ∏ _p ∈ S, (-1 : ℝ) := by
  have h := ArithmeticFunction.IsMultiplicative.map_prod (fun p : Nat.Primes => (p : ℕ))
    ArithmeticFunction.isMultiplicative_moebius S (by
      intro p _ q _ hpq
      exact (Nat.coprime_primes p.property q.property).mpr
        (fun h => hpq (Subtype.ext h)))
  rw [h]
  push_cast
  apply prod_congr rfl
  intro p _
  rw [ArithmeticFunction.moebius_apply_prime p.property]
  norm_num

private theorem subset_sqrt (S : Finset Nat.Primes) :
    (∏ p ∈ S, Real.sqrt (p : ℝ)) = Real.sqrt ((∏ p ∈ S, (p : ℕ)) : ℝ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [prod_insert hp, prod_insert hp, Real.sqrt_mul (Nat.cast_nonneg _), ih]

private theorem subset_gain (S : Finset Nat.Primes) :
    (∏ p ∈ S, -primeGain 0 p) =
      ((ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) : ℤ) : ℝ)/
        Real.sqrt ((∏ p ∈ S, (p : ℕ)) : ℝ) := by
  simp only [primeGain, damping, neg_zero, zero_mul, zero_div, Real.exp_zero, ← neg_div]
  rw [prod_div_distrib, subset_sqrt, subset_moebius]

private theorem subset_exp_log (S : Finset Nat.Primes) :
    Real.exp (∑ p ∈ S, Real.log (p : ℝ)) = ((∏ p ∈ S, (p : ℕ)) : ℝ) := by
  rw [Real.exp_sum]
  apply prod_congr rfl
  intro p _
  exact Real.exp_log (by exact_mod_cast p.property.pos)

/-- Each individual channel has its original Möbius coefficient and
unit-source argument, before any sum or covariance is formed. -/
theorem nativePrimeChannel_eq_divisor (S : Finset Nat.Primes) (t : ℝ) :
    nativePrimeChannel S t =
      ((ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) : ℤ) : ℝ)*
        Real.sqrt ((∏ p ∈ S, (p : ℕ)) : ℝ)*
          divisorContinuousUnitHead (Real.exp t/((∏ p ∈ S, (p : ℕ)) : ℝ))/Real.exp t := by
  have hdN : 0 < ∏ p ∈ S, (p : ℕ) := prod_pos (fun p _ => p.property.pos)
  have hd : (0 : ℝ) < ((∏ p ∈ S, (p : ℕ)) : ℝ) := by exact_mod_cast hdN
  have hs : Real.sqrt ((∏ p ∈ S, (p : ℕ)) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hdiv : ((∏ p ∈ S, (p : ℕ)) : ℝ)/Real.sqrt ((∏ p ∈ S, (p : ℕ)) : ℝ) =
      Real.sqrt ((∏ p ∈ S, (p : ℕ)) : ℝ) := by
    apply (div_eq_iff hs).mpr
    rw [← sq, Real.sq_sqrt hd.le]
  unfold nativePrimeChannel
  rw [subset_gain]
  simp only [unitClockSource, damping, neg_zero, zero_mul, zero_div, Real.exp_zero, one_mul]
  rw [mobiusDivisorCriticalClockHead]
  simp only [mobiusDivisorContinuousHead, prod_empty, Nat.divisors_one, sum_singleton,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, Real.sqrt_one, one_mul,
    Nat.cast_one, div_one]
  rw [Real.exp_sub, subset_exp_log]
  calc
    _ = ((ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) : ℤ) : ℝ)*
        (((∏ p ∈ S, (p : ℕ)) : ℝ)/Real.sqrt ((∏ p ∈ S, (p : ℕ)) : ℝ))*
          divisorContinuousUnitHead (Real.exp t/((∏ p ∈ S, (p : ℕ)) : ℝ))/Real.exp t := by
      field_simp
    _ = _ := by rw [hdiv]

end RHTower.RoutePWindow
