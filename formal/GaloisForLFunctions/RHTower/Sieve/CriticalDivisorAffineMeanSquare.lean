import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition

/-!
# Off-diagonal-free mean square for the critical divisor carrier

The conductor-length Dirichlet polynomial for `ζ(s)²` has coefficients `d(n)n⁻¹ᐟ²`.  Applying the
general affine mean-square theorem directly avoids an explicit off-diagonal estimate.  Its two
coefficient prices are

`∑_{n≤N} n |d(n)n⁻¹ᐟ²|² = ∑_{n≤N} d(n)² ≤ N(1+log N)³`,

`∑_{n≤N} |d(n)n⁻¹ᐟ²|² = ∑_{n≤N} d(n)²/n ≤ (1+log N)⁴`.

The first is the existing fixed divisor-moment theorem.  For the second, this file proves the
stronger harmonic generalized-divisor law

`∑_{n≤N} d_r(n)/n ≤ H_N^r`.

Consequently the critical divisor carrier has mean square `O(N log³N + T log⁴N)` with explicit
constants.  At conductor length `N ≍ T`, this is exactly the critical zeta fourth-moment scale.  The
remaining Route-T obstacle is transfer from the exact smooth AFE to this carrier, not a raw
off-diagonal sum.
-/

open Complex MeasureTheory Set Finset

namespace RHTower.Sieve

noncomputable section

open scoped ArithmeticFunction.zeta

/-- Harmonic tilt `f(n)/n` of a natural-valued arithmetic function. -/
def harmonicTiltNat (f : ArithmeticFunction ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (f n : ℝ) / (n : ℝ), by simp⟩

theorem harmonicTiltNat_apply (f : ArithmeticFunction ℕ) (n : ℕ) :
    harmonicTiltNat f n = (f n : ℝ) / (n : ℝ) := rfl

/-- Harmonic tilt turns Dirichlet convolution into convolution after casting to `ℝ`. -/
theorem harmonicTiltNat_mul_apply (f g : ArithmeticFunction ℕ) (m : ℕ) :
    (harmonicTiltNat f * harmonicTiltNat g) m =
      ((f * g) m : ℝ) / (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hprod, hm0⟩ := Nat.mem_divisorsAntidiagonal.1 hp
  rw [harmonicTiltNat_apply, harmonicTiltNat_apply, div_mul_div_comm]
  congr 1
  · push_cast
    rfl
  · rw [← Nat.cast_mul, hprod]

/-- Harmonic partial sum of the `r`-fold zeta-convolution coefficients. -/
def generalizedDivisorHarmonicSum (r N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) / (n : ℝ)

/-- Exact harmonic hyperbola recurrence for generalized divisor coefficients. -/
theorem generalizedDivisorHarmonicSum_succ (r N : ℕ) :
    generalizedDivisorHarmonicSum (r + 1) N =
      ∑ d ∈ Finset.Icc 1 N, (1 / (d : ℝ)) * generalizedDivisorHarmonicSum r (N / d) := by
  rw [generalizedDivisorHarmonicSum]
  rw [show (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 1) =
      ArithmeticFunction.zeta *
        (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r by rw [pow_succ']]
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ) / (n : ℝ) =
        (harmonicTiltNat (ArithmeticFunction.zeta : ArithmeticFunction ℕ) *
          harmonicTiltNat ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r)) n := by
    intro n hn
    exact (harmonicTiltNat_mul_apply
      (ArithmeticFunction.zeta : ArithmeticFunction ℕ)
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n).symm
  rw [Finset.sum_congr rfl hpoint]
  rw [RHTower.sum_Icc_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [harmonicTiltNat_apply]
  have hd0 : d ≠ 0 := by
    rw [Finset.mem_Icc] at hd
    omega
  rw [ArithmeticFunction.zeta_apply_ne hd0]
  simp only [Nat.cast_one, one_div]
  congr 1

/-- The `r`-fold generalized divisor harmonic sum is at most `H_N^r`. -/
theorem generalizedDivisorHarmonicSum_le_harmonic_pow
    (r N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    generalizedDivisorHarmonicSum r N ≤ ((harmonic N : ℚ) : ℝ) ^ r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction k generalizing N with
  | zero =>
      rw [generalizedDivisorHarmonicSum]
      have hsum :
          ∑ n ∈ Finset.Icc 1 N,
              (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 1) n : ℝ) / (n : ℝ) =
            ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := by
          rw [Finset.mem_Icc] at hn
          omega
        simp [ArithmeticFunction.zeta_apply, hn0]
      rw [hsum, sum_Icc_one_div_eq_harmonic]
      simp
  | succ k ih =>
      rw [show 1 + (k + 1) = (1 + k) + 1 by omega]
      rw [generalizedDivisorHarmonicSum_succ]
      have hH0 : 0 ≤ ((harmonic N : ℚ) : ℝ) := by
        have hz := harmonic_cast_mono (Nat.zero_le N)
        simpa using hz
      calc
        ∑ d ∈ Finset.Icc 1 N, (1 / (d : ℝ)) *
              generalizedDivisorHarmonicSum (1 + k) (N / d)
            ≤ ∑ d ∈ Finset.Icc 1 N, (1 / (d : ℝ)) *
                (((harmonic N : ℚ) : ℝ) ^ (1 + k)) := by
              apply Finset.sum_le_sum
              intro d hd
              have hdmem := Finset.mem_Icc.mp hd
              have hNd : 1 ≤ N / d :=
                (Nat.one_le_div_iff (by omega)).mpr hdmem.2
              have hinner := ih (N / d) hNd (by omega)
              have hmono := harmonic_cast_mono (Nat.div_le_self N d)
              have hsmall0 : 0 ≤ ((harmonic (N / d) : ℚ) : ℝ) := by
                have hz := harmonic_cast_mono (Nat.zero_le (N / d))
                simpa using hz
              have hpow := pow_le_pow_left₀ hsmall0 hmono (1 + k)
              exact mul_le_mul_of_nonneg_left (hinner.trans hpow) (by positivity)
        _ = ((harmonic N : ℚ) : ℝ) ^ ((1 + k) + 1) := by
              rw [← Finset.sum_mul]
              have hsum : ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) =
                  ((harmonic N : ℚ) : ℝ) := sum_Icc_one_div_eq_harmonic N
              rw [hsum, pow_succ]
              ring

/-- Harmonic square-divisor sum with the exact fourth logarithmic power. -/
theorem sum_card_divisors_sq_div_le_polylog (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ≤
      (1 + Real.log N) ^ 4 := by
  have hcoeff : ∀ n ∈ Finset.Icc 1 N,
      (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ≤
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 4) n : ℕ) : ℝ) /
          (n : ℝ) := by
    intro n hn
    have hn0 : n ≠ 0 := by
      rw [Finset.mem_Icc] at hn
      omega
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast card_divisors_pow_le_zeta_pow 2 n hn0) (by positivity)
  calc
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 / (n : ℝ)
        ≤ generalizedDivisorHarmonicSum 4 N := by
          unfold generalizedDivisorHarmonicSum
          exact Finset.sum_le_sum hcoeff
    _ ≤ ((harmonic N : ℚ) : ℝ) ^ 4 :=
      generalizedDivisorHarmonicSum_le_harmonic_pow 4 N (by norm_num) hN
    _ ≤ (1 + Real.log N) ^ 4 := by
      have hH0 : 0 ≤ ((harmonic N : ℚ) : ℝ) := by
        have hz := harmonic_cast_mono (Nat.zero_le N)
        simpa using hz
      exact pow_le_pow_left₀ hH0 (harmonic_le_one_add_log N) 4

/-- Coefficient sequence `d(n)n⁻¹ᐟ²`, truncated at `N`. -/
noncomputable def criticalDivisorSeq (N : ℕ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 N then
    (n.divisors.card : ℂ) *
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
  else 0

theorem criticalDivisorSeq_support {N n : ℕ} (h : criticalDivisorSeq N n ≠ 0) :
    n ∈ Finset.Icc 1 N := by
  by_contra hn
  simp [criticalDivisorSeq, hn] at h

theorem criticalDivisorSeq_norm_sq (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    ‖criticalDivisorSeq N n‖ ^ 2 =
      (n.divisors.card : ℝ) ^ 2 / (n : ℝ) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [criticalDivisorSeq, if_pos hn, norm_mul, Complex.norm_natCast]
  have hpow : ‖(((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = 1 / (n : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg _ _)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hnR)]
    rw [show (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -1 by norm_num]
    rw [Real.rpow_neg_one]
    exact inv_eq_one_div _
    all_goals positivity
  rw [mul_pow, hpow]
  ring

theorem criticalDivisorSeq_weighted_mass_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖criticalDivisorSeq N n‖ ^ 2 ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  have heq :
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖criticalDivisorSeq N n‖ ^ 2 =
        ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [criticalDivisorSeq_norm_sq N n hn]
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)
    field_simp
  rw [heq]
  simpa using sum_card_divisors_pow_le_polylog 2 N hN

theorem criticalDivisorSeq_plain_mass_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ‖criticalDivisorSeq N n‖ ^ 2 ≤
      (1 + Real.log N) ^ 4 := by
  rw [Finset.sum_congr rfl fun n hn => criticalDivisorSeq_norm_sq N n hn]
  exact sum_card_divisors_sq_div_le_polylog N hN

theorem criticalDivisorSeq_generalMeanSquareConst_le (N : ℕ) (hN : 1 ≤ N) :
    generalMeanSquareConst (criticalDivisorSeq N) (Finset.Icc 1 N) 0 ≤
      5 * Real.pi * Real.exp 1 * ((N : ℝ) * (1 + Real.log N) ^ 3) := by
  rw [generalMeanSquareConst]
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  exact mul_le_mul_of_nonneg_left (criticalDivisorSeq_weighted_mass_le N hN) (by positivity)

theorem criticalDivisorSeq_generalMeanSquareRate_le (N : ℕ) (hN : 1 ≤ N) :
    generalMeanSquareRate (criticalDivisorSeq N) (Finset.Icc 1 N) 0 ≤
      (5 * Real.pi / 2) * (1 + Real.log N) ^ 4 := by
  rw [generalMeanSquareRate]
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  exact mul_le_mul_of_nonneg_left (criticalDivisorSeq_plain_mass_le N hN) (by positivity)

/-- Critical-line conductor polynomial for the square of zeta. -/
noncomputable def criticalDivisorPolynomial (N : ℕ) (t : ℝ) : ℂ :=
  LSeries (criticalDivisorSeq N) (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)

/-- The carrier is the explicit finite divisor polynomial at `1/2+it`. -/
theorem criticalDivisorPolynomial_eq_sum (N : ℕ) (t : ℝ) :
    criticalDivisorPolynomial N t =
      ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℂ) *
        (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [criticalDivisorPolynomial, LSeries_eq_sum_term_of_support
    (fun n h => criticalDivisorSeq_support h)]
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [LSeries.term_def, if_neg hn0]
  rw [criticalDivisorSeq, if_pos hnmem]
  have hpoint :
      -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (((-(1 : ℝ) / 2 : ℝ) : ℂ)) + (-((t : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [show (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I by norm_num]
  rw [hpoint, Complex.cpow_add _ _ hnC]
  have hamp : (n : ℂ) ^ (((-(1 : ℝ) / 2 : ℝ) : ℂ)) =
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow hnR.le (-(1 : ℝ) / 2)).symm
  rw [hamp]
  rw [Complex.cpow_neg]
  ring

/-- **Off-diagonal-free critical fourth carrier.**  The conductor-length divisor polynomial has
mean square `O(N log³N + T log⁴N)` with explicit constants. -/
theorem integral_Icc_normSq_criticalDivisorPolynomial_le
    (N : ℕ) (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖criticalDivisorPolynomial N t‖ ^ 2) ≤
      5 * Real.pi * Real.exp 1 * ((N : ℝ) * (1 + Real.log N) ^ 3) +
        (5 * Real.pi / 2) * (1 + Real.log N) ^ 4 * T := by
  have hbase := integral_Icc_normSq_LSeries_le_general_affine
    (a := criticalDivisorSeq N) (s := Finset.Icc 1 N)
    (by simp) (fun _n hn => criticalDivisorSeq_support hn) 0 hT
  exact hbase.trans (add_le_add
    (criticalDivisorSeq_generalMeanSquareConst_le N hN)
    (mul_le_mul_of_nonneg_right
      (criticalDivisorSeq_generalMeanSquareRate_le N hN) (by linarith)))

end

end RHTower.Sieve
