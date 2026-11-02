import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimeFlipHasAPositiveDivisorCount

/-!
# Positive divisor counts for real multiplicative contractions

The divisor convolution with one stays nonnegative when prime values range throughout
`[-1,1]`, including the zero values introduced by removing small primes. Finite geometric
sums give the local positivity; the divisor count and its rounding error give a universal
lower bound of minus one for harmonic partial sums.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

private theorem contraction_geometric_sum_nonneg {x : ℝ} (hx : |x| ≤ 1) (k : ℕ) :
    0 ≤ ∑ j ∈ range (k + 1), x ^ j := by
  rcases le_or_gt 0 x with hx0 | hx0
  · exact sum_nonneg fun _ _ => pow_nonneg hx0 _
  have hgeom := geom_sum_mul x (k + 1)
  have hpow : x ^ (k + 1) ≤ 1 := by
    calc
      _ ≤ |x ^ (k + 1)| := le_abs_self _
      _ = |x| ^ (k + 1) := abs_pow _ _
      _ ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  apply le_of_mul_le_mul_left (a := 1 - x) ?_ (by linarith only [hx0])
  nlinarith only [hgeom, hpow]

private theorem contraction_pow {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n)
    {p : ℕ} (hp : p ≠ 0) (k : ℕ) : ω (p ^ k) = ω p ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using h1
  | succ k ih => rw [pow_succ, hmul _ _ (pow_ne_zero _ hp) hp, ih, pow_succ]

private theorem contractionArithmeticFunction_multiplicative {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n) :
    (signArithmeticFunction ω).IsMultiplicative := by
  constructor
  · simpa only [signArithmeticFunction, ArithmeticFunction.coe_mk, if_false,
      Nat.one_ne_zero] using h1
  · intro m n _
    rcases eq_or_ne m 0 with rfl | hm
    · simp [signArithmeticFunction]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [signArithmeticFunction]
    simpa only [signArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)] using hmul m n hm hn

/-- Real completely multiplicative functions bounded by one have nonnegative divisor sums. -/
theorem contractionDivisorCount_nonneg {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n)
    (hbd : ∀ n, |ω n| ≤ 1) (n : ℕ) : 0 ≤ signDivisorCount ω n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [signDivisorCount]
  let g := signArithmeticFunction ω * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hg : g.IsMultiplicative := (contractionArithmeticFunction_multiplicative h1 hmul).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast
  rw [signDivisorCount_eq_convolution, hg.multiplicative_factorization g hn]
  change 0 ≤ ∏ p ∈ n.factorization.support, g (p ^ n.factorization p)
  apply prod_nonneg
  intro p hp
  have hprime : p.Prime :=
    Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hp)
  rw [← signDivisorCount_eq_convolution, signDivisorCount, Nat.sum_divisors_prime_pow hprime]
  simp_rw [contraction_pow h1 hmul hprime.ne_zero]
  exact contraction_geometric_sum_nonneg (hbd p) _

/-- The divisor-count rounding estimate only needs bounded coefficients. -/
theorem abs_mul_harmonicSum_sub_divisorCount_le_of_abs_le_one {ω : ℕ → ℝ}
    (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) :
    |(N : ℝ) * gaugeHarmonicSum ω N - ∑ n ∈ Icc 1 N, signDivisorCount ω n| ≤ N := by
  rw [sum_signDivisorCount_eq, gaugeHarmonicSum, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, |(N : ℝ) * (ω d / d) - ω d * (N / d : ℕ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Icc 1 N, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hdN : 0 < d := (mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdN
      have hlow : 0 ≤ (N : ℝ) / d - (N / d : ℕ) := sub_nonneg.mpr Nat.cast_div_le
      have hround : (N : ℝ) < (N / d : ℕ) * (d : ℝ) + d := by
        exact_mod_cast Nat.lt_div_mul_add (a := N) (b := d) hdN
      have hquot : (N : ℝ) / d ≤ (N / d : ℕ) + 1 := by
        apply (div_le_iff₀ hdR).mpr
        nlinarith only [hround]
      have hhigh : (N : ℝ) / d - (N / d : ℕ) ≤ 1 := by linarith only [hquot]
      calc
        _ = |ω d| * ((N : ℝ) / d - (N / d : ℕ)) := by
          rw [show (N : ℝ) * (ω d / d) - ω d * (N / d : ℕ) =
            ω d * ((N : ℝ) / d - (N / d : ℕ)) by ring, abs_mul, abs_of_nonneg hlow]
        _ ≤ 1 * 1 := mul_le_mul (hbd d) hhigh hlow zero_le_one
        _ = 1 := one_mul _
    _ = N := by simp

/-- A real completely multiplicative contraction has every harmonic partial sum at least
minus one. This includes gauges that vanish on all integers divisible by a removed prime. -/
theorem neg_one_le_harmonicSum_of_real_multiplicative {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n)
    (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) : -1 ≤ gaugeHarmonicSum ω N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [gaugeHarmonicSum]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hbound := (abs_le.mp (abs_mul_harmonicSum_sub_divisorCount_le_of_abs_le_one hbd N)).1
  have hcount : 0 ≤ ∑ n ∈ Icc 1 N, signDivisorCount ω n :=
    sum_nonneg fun n _ => contractionDivisorCount_nonneg h1 hmul hbd n
  nlinarith only [hNpos, hbound, hcount]

end GaloisForLFunctions.ArithmeticCountingPositivity

