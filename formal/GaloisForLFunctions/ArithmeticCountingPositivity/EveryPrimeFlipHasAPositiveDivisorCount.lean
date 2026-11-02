import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# Positive divisor counts for real sign gauges

Convolution with the constant-one arithmetic function removes the signs: each prime-power
factor is either its number of divisors or an alternating sum equal to zero or one.
The exact divisor swap then compares this positive count with the signed harmonic sum.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- A sign gauge as an arithmetic function, with its irrelevant value at zero removed. -/
def signArithmeticFunction (ω : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else ω n, by simp⟩

/-- The divisor convolution of a real sign gauge with the constant-one function. -/
def signDivisorCount (ω : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, ω d

private theorem sign_one {ω : ℕ → ℝ} (hω : IsSignGauge ω) : ω 1 = 1 := by
  have h := hω.mul (m := 1) (n := 1) (by decide) (by decide)
  simpa only [one_mul, hω.mul_self (by decide : 1 ≠ 0)] using h

private theorem sign_pow {ω : ℕ → ℝ} (hω : IsSignGauge ω)
    {p : ℕ} (hp : p ≠ 0) (k : ℕ) : ω (p ^ k) = ω p ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using sign_one hω
  | succ k ih => rw [pow_succ, hω.mul (pow_ne_zero _ hp) hp, ih, pow_succ]

private theorem signArithmeticFunction_multiplicative {ω : ℕ → ℝ}
    (hω : IsSignGauge ω) : (signArithmeticFunction ω).IsMultiplicative := by
  constructor
  · simpa only [signArithmeticFunction, ArithmeticFunction.coe_mk, if_false,
      Nat.one_ne_zero] using sign_one hω
  · intro m n _
    rcases eq_or_ne m 0 with rfl | hm
    · simp [signArithmeticFunction]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [signArithmeticFunction]
    simpa only [signArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)] using hω.mul hm hn

/-- The literal divisor sum agrees with Dirichlet convolution by the constant-one function. -/
theorem signDivisorCount_eq_convolution (ω : ℕ → ℝ) (n : ℕ) :
    signDivisorCount ω n =
      (signArithmeticFunction ω * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact sum_congr rfl fun d hd => by
    simp only [signArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']

private theorem sign_geometric_sum_nonneg {x : ℝ} (hx : x * x = 1) (k : ℕ) :
    0 ≤ ∑ j ∈ range (k + 1), x ^ j := by
  have hxabs : |x| = 1 := abs_eq_one_of_mul_self_eq_one hx
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hxabs with hx1 | hxm
  · subst x
    exact sum_nonneg fun _ _ => by positivity
  · subst x
    have hgeom := geom_sum_mul (-1 : ℝ) (k + 1)
    have hpow : (-1 : ℝ) ^ (k + 1) ≤ 1 := by
      calc
        _ ≤ |(-1 : ℝ) ^ (k + 1)| := le_abs_self _
        _ = 1 := by rw [abs_pow]; simp only [abs_neg, abs_one, one_pow]
    nlinarith only [hgeom, hpow]

/-- Every prime-power divisor count is nonnegative, even when that prime is flipped. -/
theorem signDivisorCount_prime_pow_nonneg {ω : ℕ → ℝ} (hω : IsSignGauge ω)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ signDivisorCount ω (p ^ k) := by
  rw [signDivisorCount, Nat.sum_divisors_prime_pow hp]
  simp_rw [sign_pow hω hp.ne_zero]
  exact sign_geometric_sum_nonneg (hω.mul_self hp.ne_zero) k

/-- The divisor convolution of every real sign gauge is nonnegative at every integer. -/
theorem signDivisorCount_nonneg {ω : ℕ → ℝ} (hω : IsSignGauge ω) (n : ℕ) :
    0 ≤ signDivisorCount ω n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [signDivisorCount]
  let g := signArithmeticFunction ω * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hg : g.IsMultiplicative :=
    (signArithmeticFunction_multiplicative hω).mul
      ArithmeticFunction.isMultiplicative_zeta.natCast
  rw [signDivisorCount_eq_convolution, hg.multiplicative_factorization g hn]
  change 0 ≤ ∏ p ∈ n.factorization.support, g (p ^ n.factorization p)
  apply prod_nonneg
  intro p hp
  rw [← signDivisorCount_eq_convolution]
  exact signDivisorCount_prime_pow_nonneg hω
    (Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hp)) _

/-- Counting multiples gives the exact unsmoothed positive divisor count. -/
theorem sum_signDivisorCount_eq (ω : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, signDivisorCount ω n =
      ∑ d ∈ Icc 1 N, ω d * (N / d : ℕ) := by
  unfold signDivisorCount
  rw [RHTower.Sieve.sum_divisors_swap N (fun d _ => ω d)]
  refine sum_congr rfl fun d _ => ?_
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]

private theorem quotient_remainder_bounds (N : ℕ) {d : ℕ} (hd : 0 < d) :
    0 ≤ (N : ℝ) / d - (N / d : ℕ) ∧ (N : ℝ) / d - (N / d : ℕ) ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
  have heq : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by
    exact_mod_cast Nat.mod_add_div N d
  have hr : (N : ℝ) / d - (N / d : ℕ) = ((N % d : ℕ) : ℝ) / d := by
    apply (eq_div_iff hdR.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hdR.ne']
    linarith only [heq]
  rw [hr]
  exact ⟨div_nonneg (Nat.cast_nonneg _) hdR.le, (div_le_one hdR).mpr hmod.le⟩

/-- The signed harmonic sum differs from the positive counting average by at most one. -/
theorem abs_mul_gaugeHarmonicSum_sub_signDivisorCount_le {ω : ℕ → ℝ}
    (hω : IsSignGauge ω) (N : ℕ) :
    |(N : ℝ) * gaugeHarmonicSum ω N - ∑ n ∈ Icc 1 N, signDivisorCount ω n| ≤ N := by
  rw [sum_signDivisorCount_eq, gaugeHarmonicSum, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, |(N : ℝ) * (ω d / d) - ω d * (N / d : ℕ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Icc 1 N, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 : d ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hd).1
      have habs : |ω d| = 1 := abs_eq_one_of_mul_self_eq_one (hω.mul_self hd0)
      have hr := quotient_remainder_bounds N (mem_Icc.mp hd).1
      calc
        _ = |ω d * ((N : ℝ) / d - (N / d : ℕ))| := by congr 1; ring
        _ = (N : ℝ) / d - (N / d : ℕ) := by rw [abs_mul, habs, one_mul, abs_of_nonneg hr.1]
        _ ≤ 1 := hr.2
    _ = N := by simp

/-- Multiplicative signs cannot make any harmonic partial sum smaller than minus one. -/
theorem neg_one_le_gaugeHarmonicSum {ω : ℕ → ℝ} (hω : IsSignGauge ω) (N : ℕ) :
    -1 ≤ gaugeHarmonicSum ω N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [gaugeHarmonicSum]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hbound := (abs_le.mp (abs_mul_gaugeHarmonicSum_sub_signDivisorCount_le hω N)).1
  have hcount : 0 ≤ ∑ n ∈ Icc 1 N, signDivisorCount ω n :=
    sum_nonneg fun n _ => signDivisorCount_nonneg hω n
  nlinarith only [hNpos, hbound, hcount]

end GaloisForLFunctions.ArithmeticCountingPositivity
