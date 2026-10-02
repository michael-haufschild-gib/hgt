import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!+# Mixed prime-dilation curvature of the centered divisor forcing

The divisor sum of the literal coefficients `Λ(n)-1` is `log n-τ(n)`.
Its square has an exact mixed prime-dilation difference. At a third prime
cofactor the difference is affine in its logarithm, with slope `-4`, and
is unbounded below. Thus pointwise nonnegative mixed curvature cannot
produce positivity of the complete centered-source covariance. The
formula retains the cofactor term that any aggregate argument must handle.
-/

noncomputable section
namespace RHTower

/-- The divisor sum of the centered von Mangoldt coefficients. -/
def xiMassCenteredDivisorForcing (n : ℕ) : ℝ :=
  Real.log n - n.divisors.card

theorem xiMassCenteredDivisorForcing_eq_divisorSum (n : ℕ) :
    xiMassCenteredDivisorForcing n =
      ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d - 1) := by
  simp only [Finset.sum_sub_distrib, ArithmeticFunction.vonMangoldt_sum,
    Finset.sum_const, nsmul_eq_mul, mul_one, xiMassCenteredDivisorForcing]

private theorem prime_divisor_card {p : ℕ} (hp : p.Prime) :
    p.divisors.card = 2 := by
  have h := ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hp
  simpa only [pow_one, ArithmeticFunction.sigma_zero_apply] using h

theorem xiMassCenteredDivisorForcing_mul {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    xiMassCenteredDivisorForcing (a * b) =
      Real.log a + Real.log b - (a.divisors.card : ℝ) * b.divisors.card := by
  simp only [xiMassCenteredDivisorForcing, hab.card_divisors_mul,
    Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]

/-- The forcing is affine along every prime-power chain with a fixed coprime cofactor. -/
theorem xiMassCenteredDivisorForcing_primePow_mul {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) (hpm : p.Coprime m) (r : ℕ) :
    xiMassCenteredDivisorForcing (p ^ r * m) =
      xiMassCenteredDivisorForcing m +
        r * (Real.log p - (m.divisors.card : ℝ)) := by
  have hcard : (p ^ r).divisors.card = r + 1 := by
    simpa only [ArithmeticFunction.sigma_zero_apply] using
      (ArithmeticFunction.sigma_zero_apply_prime_pow (i := r) hp)
  rw [xiMassCenteredDivisorForcing_mul (pow_ne_zero _ hp.ne_zero) hm (hpm.pow_left r),
    Nat.cast_pow, Real.log_pow, hcard, xiMassCenteredDivisorForcing]
  push_cast
  ring

/-- The two prime-dilation differences of the squared literal forcing. -/
def xiMassCenteredDivisorMixedCurvature (p q m : ℕ) : ℝ :=
  xiMassCenteredDivisorForcing (p * q * m) ^ 2 -
    xiMassCenteredDivisorForcing (p * m) ^ 2 -
    xiMassCenteredDivisorForcing (q * m) ^ 2 +
    xiMassCenteredDivisorForcing m ^ 2

/-- Exact cofactor-sensitive mixed curvature, before any sign estimate. -/
theorem xiMassCenteredDivisorMixedCurvature_eq {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hm : m ≠ 0)
    (hpm : p.Coprime m) (hqm : q.Coprime m) :
    xiMassCenteredDivisorMixedCurvature p q m =
      2 * Real.log p * Real.log q -
        4 * (m.divisors.card : ℝ) * (Real.log p + Real.log q) -
        2 * (m.divisors.card : ℝ) * Real.log m +
        9 * (m.divisors.card : ℝ) ^ 2 := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  rw [xiMassCenteredDivisorMixedCurvature,
    xiMassCenteredDivisorForcing_mul (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hm
      (hpm.mul_left hqm),
    xiMassCenteredDivisorForcing_mul hp.ne_zero hm hpm,
    xiMassCenteredDivisorForcing_mul hq.ne_zero hm hqm,
    hcop.card_divisors_mul, prime_divisor_card hp, prime_divisor_card hq,
    Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero)
      (Nat.cast_ne_zero.mpr hq.ne_zero), xiMassCenteredDivisorForcing]
  norm_num only [Nat.cast_ofNat]
  ring

/-- At a third prime the mixed curvature has a strictly negative logarithmic slope. -/
theorem xiMassCenteredDivisorMixedCurvature_prime {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    xiMassCenteredDivisorMixedCurvature p q r =
      2 * Real.log p * Real.log q - 8 * (Real.log p + Real.log q) -
        4 * Real.log r + 36 := by
  rw [xiMassCenteredDivisorMixedCurvature_eq hp hq hpq hr.ne_zero
    ((Nat.coprime_primes hp hr).mpr hpr) ((Nat.coprime_primes hq hr).mpr hqr),
    prime_divisor_card hr]
  norm_num only [Nat.cast_ofNat]

/-- For every pair of distinct primes, actual prime cofactors make the mixed curvature
smaller than any prescribed real value, beyond every prescribed natural cutoff. -/
theorem xiMassCenteredDivisorMixedCurvature_unboundedBelow {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (B : ℝ) (K : ℕ) :
    ∃ r : ℕ, r.Prime ∧ K < r ∧ p < r ∧ q < r ∧
      xiMassCenteredDivisorMixedCurvature p q r < B := by
  let C : ℝ := 2 * Real.log p * Real.log q - 8 * (Real.log p + Real.log q) + 36
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp ((C - B) / 4))
  obtain ⟨r, hnr, hr⟩ := Nat.exists_infinite_primes (n + p + q + K + 1)
  have hnr' : n ≤ r := by omega
  have hpr : p < r := by omega
  have hqr : q < r := by omega
  have hKr : K < r := by omega
  have hlog : (C - B) / 4 < Real.log r := by
    apply (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr hr.pos)).mpr
    exact hn.trans_le (by exact_mod_cast hnr')
  refine ⟨r, hr, hKr, hpr, hqr, ?_⟩
  rw [xiMassCenteredDivisorMixedCurvature_prime hp hq hr hpq
    (ne_of_lt hpr) (ne_of_lt hqr)]
  dsimp only [C] at hlog
  linarith

end RHTower
