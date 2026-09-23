import GaloisForLFunctions.RHTower.Sieve.SqrtLogTailIntegral
import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import Mathlib.NumberTheory.AbelSummation

/-!
# Mertens' weighted prime sum as an integral of `θ`

Summation by parts with the weight `f(t) = 1/t` turns the prime sum `∑_{p ≤ x} log p / p` into a
boundary term and an integral of Chebyshev's `θ`:

```text
mertensA ⌊x⌋ = θ(x)/x + ∫_{(2,x]} θ(t)/t² dt .
```

Both sides are elementary; the content is entirely in mathlib's `sum_mul_eq_sub_integral_mul₁`,
whose hypotheses `c 0 = c 1 = 0` are exactly the statement that neither `0` nor `1` is prime.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics MeasureTheory Set

/-- The Abel coefficient: `log p` on primes, zero elsewhere.  Its partial sums are `θ`. -/
noncomputable def primeLogCoeff (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

theorem primeLogCoeff_zero : primeLogCoeff 0 = 0 := by
  simp [primeLogCoeff, Nat.not_prime_zero]

theorem primeLogCoeff_one : primeLogCoeff 1 = 0 := by
  simp [primeLogCoeff, Nat.not_prime_one]

theorem sum_Icc_primeLogCoeff (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

theorem Icc_zero_eq_range (n : ℕ) : Finset.Icc 0 n = Finset.range (n + 1) := by
  ext k
  simp

theorem sum_Icc_inv_mul_primeLogCoeff (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, (k : ℝ)⁻¹ * primeLogCoeff k = mertensA n := by
  rw [← sum_range_primeLogWeight, Icc_zero_eq_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold primeLogCoeff primeLogWeight
  split_ifs with h
  · rw [inv_mul_eq_div]
  · rw [mul_zero]

/-- **Summation by parts for Mertens' weighted prime sum.** -/
theorem mertensA_eq_theta_div_add_setIntegral {b : ℝ} (hb : 2 ≤ b) :
    mertensA ⌊b⌋₊ = Chebyshev.theta b / b
      + ∫ t in Set.Ioc 2 b, Chebyshev.theta t / t ^ (2 : ℕ) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hderiv : ∀ t ∈ Set.Icc (2 : ℝ) b, HasDerivAt (fun x : ℝ => x⁻¹) (-(t ^ (2 : ℕ))⁻¹) t := by
    intro t ht
    exact hasDerivAt_inv (by have := ht.1; intro h; rw [h] at this; norm_num at this)
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) b, DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hderiv_eq : ∀ t ∈ Set.Icc (2 : ℝ) b, deriv (fun x : ℝ => x⁻¹) t = -(t ^ (2 : ℕ))⁻¹ :=
    fun t ht => (hderiv t ht).deriv
  have hcont : ContinuousOn (fun t : ℝ => -(t ^ (2 : ℕ))⁻¹) (Set.Icc 2 b) := by
    refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro t ht
    have h2 : (2 : ℝ) ≤ t := ht.1
    positivity
  have hint : IntegrableOn (deriv fun x : ℝ => x⁻¹) (Set.Icc 2 b) :=
    (hcont.integrableOn_Icc).congr_fun (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_integral_mul₁ primeLogCoeff primeLogCoeff_zero primeLogCoeff_one b
    hdiff hint
  rw [sum_Icc_inv_mul_primeLogCoeff, sum_Icc_primeLogCoeff] at habel
  have hinner : ∫ t in Set.Ioc 2 b, deriv (fun x : ℝ => x⁻¹) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k
      = -∫ t in Set.Ioc 2 b, Chebyshev.theta t / t ^ (2 : ℕ) := by
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have h2 : (2 : ℝ) < t := ht.1
    have hmem : t ∈ Set.Icc (2 : ℝ) b := ⟨h2.le, ht.2⟩
    rw [sum_Icc_primeLogCoeff, hderiv_eq t hmem]
    field_simp
  rw [hinner] at habel
  rw [habel, inv_mul_eq_div]
  ring

end RHTower.Sieve
