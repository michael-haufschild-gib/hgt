import GaloisForLFunctions.RHTower.RoutePFinitePrimeCovariance
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Basic

/-!
# Uniform summation of the actual prime-biased recovery costs

The mean bias is `1-1/p`. Its covariance noise, after the critical
prime-delay normalization, has a summable inverse-square cost.
The resulting constant is independent of the finite prime set and
of every additional nonnegative damping incorporated into the gain.
-/

open Finset MeasureTheory

namespace RHTower.RoutePWindow

noncomputable def meanGain (q : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  (1-1/(p : ℝ))*q p

noncomputable def noiseGain (q : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  (1-(1-1/(p : ℝ))^2)*(q p)^2

noncomputable def covarianceBudget : ℝ :=
  Real.exp (32*∑' n : ℕ, 1/(n : ℝ)^2)

theorem covarianceBudget_pos : 0 < covarianceBudget := Real.exp_pos _

/-- Uniform estimates for the actual mean and noise gains; no source
square or full-ray admission hypothesis enters this scalar estimate. -/
theorem prime_gain_bounds (q : Nat.Primes → ℝ) (p : Nat.Primes)
    (hq0 : 0 ≤ q p) (hq : q p ≤ 1/Real.sqrt (p : ℝ)) :
    0 ≤ meanGain q p ∧ meanGain q p ≤ 3/4 ∧
      0 ≤ noiseGain q p ∧ noiseGain q p ≤ 2/(p : ℝ)^2 ∧
      noiseGain q p/(1-meanGain q p)^2 ≤ 32/(p : ℝ)^2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hppos : 0 < (p : ℝ) := by linarith
  have hinv0 : 0 ≤ 1/(p : ℝ) := by positivity
  have hinv2 : 1/(p : ℝ) ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) hp2
  have hqs : (q p)^2 ≤ 1/(p : ℝ) := by
    have h := mul_self_le_mul_self hq0 hq
    simpa only [← sq, div_pow, one_pow, Real.sq_sqrt hppos.le] using h
  have hq34 : q p ≤ 3/4 := by nlinarith
  have ht0 : 0 ≤ 1-1/(p : ℝ) := by linarith
  have ht1 : 1-1/(p : ℝ) ≤ 1 := by linarith
  have hb0 : 0 ≤ meanGain q p := mul_nonneg ht0 hq0
  have hb34 : meanGain q p ≤ 3/4 :=
    (mul_le_mul_of_nonneg_right ht1 hq0).trans (by simpa using hq34)
  have hg0 : 0 ≤ 1-(1-1/(p : ℝ))^2 := by nlinarith
  have hg : 1-(1-1/(p : ℝ))^2 ≤ 2/(p : ℝ) := by
    rw [show 2/(p : ℝ) = 2*(1/(p : ℝ)) by ring]
    nlinarith [sq_nonneg (1/(p : ℝ))]
  have hw0 : 0 ≤ noiseGain q p := mul_nonneg hg0 (sq_nonneg _)
  have hw : noiseGain q p ≤ 2/(p : ℝ)^2 := by
    calc
      _ ≤ (2/(p : ℝ))*(1/(p : ℝ)) :=
        mul_le_mul hg hqs (sq_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨hb0, hb34, hw0, hw, ?_⟩
  have hden : (1/16 : ℝ) ≤ (1-meanGain q p)^2 := by nlinarith
  calc
    _ ≤ noiseGain q p/(1/16) :=
      div_le_div_of_nonneg_left hw0 (by norm_num) hden
    _ = 16*noiseGain q p := by ring
    _ ≤ 16*(2/(p : ℝ)^2) := mul_le_mul_of_nonneg_left hw (by norm_num)
    _ = _ := by ring

private theorem sum_prime_inverse_square_le (P : Finset Nat.Primes) :
    (∑ p ∈ P, 1/(p : ℝ)^2) ≤ ∑' n : ℕ, 1/(n : ℝ)^2 := by
  have hs : Summable (fun n : ℕ => 1/(n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  calc
    _ = ∑ n ∈ P.image (fun p : Nat.Primes => (p : ℕ)), 1/(n : ℝ)^2 := by
      rw [sum_image]
      intro p _ q _ hpq
      exact Subtype.ext hpq
    _ ≤ _ := hs.sum_le_tsum _ (fun _ _ => by positivity)

theorem prime_recovery_product_le (P : Finset Nat.Primes) (q : Nat.Primes → ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq : ∀ p, q p ≤ 1/Real.sqrt (p : ℝ)) :
    (∏ p ∈ P, (1+noiseGain q p/(1-meanGain q p)^2)) ≤ covarianceBudget := by
  have hw (p : Nat.Primes) : 0 ≤ noiseGain q p/(1-meanGain q p)^2 :=
    div_nonneg (prime_gain_bounds q p (hq0 p) (hq p)).2.2.1 (sq_nonneg _)
  calc
    _ ≤ Real.exp (∑ p ∈ P, noiseGain q p/(1-meanGain q p)^2) :=
      Real.prod_one_add_le_exp_sum P hw
    _ ≤ Real.exp (∑ p ∈ P, 32/(p : ℝ)^2) := by
      apply Real.exp_le_exp.mpr
      exact sum_le_sum (fun p _ => (prime_gain_bounds q p (hq0 p) (hq p)).2.2.2.2)
    _ = Real.exp (32*(∑ p ∈ P, 1/(p : ℝ)^2)) := by
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ covarianceBudget := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sum_prime_inverse_square_le P) (by norm_num))

/-- One constant controls the extra covariance cost on every finite window,
for every finite prime set and every damped critical prime gain. -/
theorem integral_prime_covariance_le (P : Finset Nat.Primes) (q : Nat.Primes → ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq : ∀ p, q p ≤ 1/Real.sqrt (p : ℝ))
    (f : ℝ → ℝ) (hf : Continuous f) (hz : ∀ t ≤ 0, f t = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      covariance P (fun p => Real.log (p : ℝ)) (meanGain q) (noiseGain q) f t) ≤
      covarianceBudget*(∫ t in (0 : ℝ)..T,
        (head P (fun p => Real.log (p : ℝ)) (meanGain q) f t)^2) := by
  have hg := fun p => prime_gain_bounds q p (hq0 p) (hq p)
  have ha (p : Nat.Primes) : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast p.property.one_lt.le
  exact (integral_covariance_le P _ _ _ ha (fun p => (hg p).1)
    (fun p => lt_of_le_of_lt (hg p).2.1 (by norm_num))
    (fun p => (hg p).2.2.1) f hf hz hT).trans
      (mul_le_mul_of_nonneg_right (prime_recovery_product_le P q hq0 hq)
        (intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)))

end RHTower.RoutePWindow
