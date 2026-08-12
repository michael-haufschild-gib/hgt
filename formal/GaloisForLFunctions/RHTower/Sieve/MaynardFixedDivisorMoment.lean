import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Fixed divisor moments for Maynard's raised factors

Maynard's bounded-degree decomposition only raises a grouped factor a bounded number of times.
The usual pointwise estimate `d(n)^K \ll_K n^ε` is therefore wasteful near the moving
zero-free edge: its constant is not uniform as `ε → 0`.

This file replaces that loss by the unconditional fixed-moment estimate

`∑_{n ≤ N} d(n)^K ≤ N (1 + log N)^(2^K - 1)`.

The proof is coefficient-exact.  The `r`-fold Dirichlet convolution power of zeta has prime-power
coefficient `multichoose r a`; the local inequality `(a+1)^K ≤ multichoose (2^K) a` dominates
`d(n)^K`.  Repeated use of the hyperbola summatory identity then bounds the convolution power by
`N H_N^(r-1)`.  All constants are explicit and independent of a moving exponent.
-/

namespace RHTower.Sieve

open scoped ArithmeticFunction.zeta
open Finset ArithmeticFunction

/-- The `r`-fold Dirichlet-convolution power of zeta has the expected stars-and-bars
coefficient at a prime power. -/
theorem zeta_pow_apply_prime_pow (r a p : ℕ) (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) (p ^ a) =
      r.multichoose a := by
  induction r generalizing a with
  | zero =>
      cases a with
      | zero => simp
      | succ a => simp [Nat.multichoose_zero_succ, hp.ne_one]
  | succ r ih =>
      rw [pow_succ, ArithmeticFunction.mul_zeta_apply,
        Nat.divisors_prime_pow hp]
      simp only [Finset.sum_map, Function.Embedding.coeFn_mk, ih]
      rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
      have hs := Nat.choose_symm (n := a + r) (k := r) (by omega)
      rw [show r + 1 + a - 1 = a + r by omega]
      simpa using hs.symm

/-- A discrete chord bound for powers on the positive integers.  Its linear coefficient
`2^K - 1` is exactly what makes the multichoose domination close uniformly in the exponent. -/
theorem mul_succ_pow_le_shift_mul_pow (x K : ℕ) (hx : 1 ≤ x) :
    x * (x + 1) ^ K ≤ (x + 2 ^ K - 1) * x ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hpow : 1 ≤ 2 ^ K := Nat.one_le_two_pow
      calc
        x * (x + 1) ^ (K + 1) = (x + 1) * (x * (x + 1) ^ K) := by ring
        _ ≤ (x + 1) * ((x + 2 ^ K - 1) * x ^ K) :=
          Nat.mul_le_mul_left (x + 1) ih
        _ ≤ (x + 2 ^ (K + 1) - 1) * x ^ (K + 1) := by
          rw [pow_succ]
          rw [show x ^ (K + 1) = x ^ K * x by simp [pow_succ]]
          have hsub : x + 2 ^ K - 1 = x + (2 ^ K - 1) := by omega
          have hsub' : x + 2 ^ K * 2 - 1 = x + (2 ^ K * 2 - 1) := by omega
          have hy : 2 ^ K - 1 + 1 = 2 ^ K := by omega
          have hy' : 2 ^ K * 2 - 1 + 1 = 2 ^ K * 2 := by omega
          have hcoeff : (x + 1) * (x + 2 ^ K - 1) ≤
              (x + 2 ^ K * 2 - 1) * x := by
            rw [hsub, hsub']
            nlinarith
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            Nat.mul_le_mul_right (x ^ K) hcoeff

/-- Exact adjacent-coefficient ratio for positive-order multichoose numbers. -/
theorem multichoose_succ_ratio (R a : ℕ) (hR : 1 ≤ R) :
    (a + 1) * R.multichoose (a + 1) =
      (a + R) * R.multichoose a := by
  rw [Nat.multichoose_eq, Nat.multichoose_eq]
  have h := Nat.add_one_mul_choose_eq (R + a - 1) a
  have htop : R + a - 1 + 1 = R + a := by omega
  rw [htop] at h
  rw [show R + (a + 1) - 1 = R + a by omega]
  nlinarith

/-- **Local fixed-moment domination.**  The `K`-th power of a prime-power divisor count is
bounded by the corresponding coefficient of the `2^K`-fold zeta convolution. -/
theorem pow_succ_le_multichoose_two_pow (K a : ℕ) :
    (a + 1) ^ K ≤ (2 ^ K).multichoose a := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hchord := mul_succ_pow_le_shift_mul_pow (a + 1) K (by omega)
      have hscale := Nat.mul_le_mul_left (a + 2 ^ K) ih
      have hratio := multichoose_succ_ratio (2 ^ K) a Nat.one_le_two_pow
      have hmul : (a + 1) * (a + 1 + 1) ^ K ≤
          (a + 1) * (2 ^ K).multichoose (a + 1) := calc
        (a + 1) * (a + 1 + 1) ^ K
            ≤ (a + 1 + 2 ^ K - 1) * (a + 1) ^ K := hchord
        _ = (a + 2 ^ K) * (a + 1) ^ K := by
          have hpow : 1 ≤ 2 ^ K := Nat.one_le_two_pow
          rw [show a + 1 + 2 ^ K - 1 = a + 2 ^ K by omega]
        _ ≤ (a + 2 ^ K) * (2 ^ K).multichoose a := hscale
        _ = (a + 1) * (2 ^ K).multichoose (a + 1) := hratio.symm
      exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- Global coefficient domination obtained by multiplying the local prime-power bounds. -/
theorem card_divisors_pow_le_zeta_pow (K n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ K ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (2 ^ K)) n := by
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (2 ^ K))
    ArithmeticFunction.isMultiplicative_zeta.pow hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_le_prod
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    rw [zeta_pow_apply_prime_pow (2 ^ K) (n.factorization p) p
      (Nat.prime_of_mem_primeFactors hp)]
    exact pow_succ_le_multichoose_two_pow K (n.factorization p)

/-- Partial sum of the coefficients of an `r`-fold zeta convolution. -/
def generalizedDivisorNatSum (r N : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n

/-- Exact hyperbola recurrence for generalized divisor sums. -/
theorem generalizedDivisorNatSum_succ (r N : ℕ) :
    generalizedDivisorNatSum (r + 1) N =
      ∑ d ∈ Finset.Icc 1 N, generalizedDivisorNatSum r (N / d) := by
  rw [generalizedDivisorNatSum]
  rw [show (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 1) =
      ArithmeticFunction.zeta *
        (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r by
    rw [pow_succ']]
  rw [RHTower.sum_Icc_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ArithmeticFunction.zeta_apply_ne (by
    rw [Finset.mem_Icc] at hd
    omega)]
  simp [generalizedDivisorNatSum]

/-- Real casts of harmonic numbers are monotone. -/
theorem harmonic_cast_mono {m n : ℕ} (hmn : m ≤ n) :
    ((harmonic m : ℚ) : ℝ) ≤ ((harmonic n : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc,
    Rat.cast_sum, Rat.cast_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl hmn)
  intro i hi him
  positivity

/-- Repeated hyperbola summation bounds the `k+1` generalized divisor sum by `N H_N^k`. -/
theorem generalizedDivisorNatSum_cast_le_harmonic (k N : ℕ) (hN : 1 ≤ N) :
    (generalizedDivisorNatSum (k + 1) N : ℝ) ≤
      (N : ℝ) * (((harmonic N : ℚ) : ℝ) ^ k) := by
  induction k generalizing N with
  | zero =>
      rw [generalizedDivisorNatSum]
      push_cast
      calc
        ∑ x ∈ Finset.Icc 1 N,
            (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (0 + 1)) x : ℝ)
            = ∑ _x ∈ Finset.Icc 1 N, (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.mem_Icc] at hx
                have hx0 : x ≠ 0 := by omega
                simp [ArithmeticFunction.zeta_apply, hx0]
        _ = (N : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
              push_cast
              norm_num
        _ ≤ (N : ℝ) * (((harmonic N : ℚ) : ℝ) ^ 0) := by simp
  | succ k ih =>
      rw [generalizedDivisorNatSum_succ]
      push_cast
      calc
        ∑ d ∈ Finset.Icc 1 N,
            (generalizedDivisorNatSum (k + 1) (N / d) : ℝ)
            ≤ ∑ d ∈ Finset.Icc 1 N,
                ((N / d : ℕ) : ℝ) *
                  (((harmonic (N / d) : ℚ) : ℝ) ^ k) := by
              apply Finset.sum_le_sum
              intro d hd
              rw [Finset.mem_Icc] at hd
              exact ih (N / d) ((Nat.one_le_div_iff (by omega)).mpr hd.2)
        _ ≤ ∑ d ∈ Finset.Icc 1 N,
              ((N : ℝ) / (d : ℝ)) *
                (((harmonic N : ℚ) : ℝ) ^ k) := by
              apply Finset.sum_le_sum
              intro d hd
              rw [Finset.mem_Icc] at hd
              have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) :=
                Nat.cast_div_le
              have hhar := harmonic_cast_mono (Nat.div_le_self N d)
              have hhar0 : 0 ≤ (((harmonic (N / d) : ℚ) : ℝ)) := by
                have hz := harmonic_cast_mono (Nat.zero_le (N / d))
                simpa using hz
              exact mul_le_mul hdiv (pow_le_pow_left₀ hhar0 hhar k)
                (pow_nonneg hhar0 k) (by positivity)
        _ = (N : ℝ) * (((harmonic N : ℚ) : ℝ) ^ k) *
              ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro d hd
              rw [div_eq_mul_inv]
              ring
        _ = (N : ℝ) * (((harmonic N : ℚ) : ℝ) ^ (k + 1)) := by
              have hsum : ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ =
                  ((harmonic N : ℚ) : ℝ) := by
                rw [harmonic_eq_sum_Icc, Rat.cast_sum]
                simp only [Rat.cast_inv, Rat.cast_natCast]
              rw [hsum]
              rw [pow_succ]
              ring

/-- **Fixed divisor moment.**  Every fixed divisor moment has an explicit `N` times polylogarithm
bound.  Unlike a pointwise `n^ε` estimate, this bound remains usable when the analytic saving tends
to zero with height. -/
theorem sum_card_divisors_pow_le_polylog (K N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ K) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by
  have hpow : 2 ^ K - 1 + 1 = 2 ^ K := by
    have := Nat.one_le_two_pow (n := K)
    omega
  have hhar0 : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    have hz := harmonic_cast_mono (Nat.zero_le N)
    simpa using hz
  calc
    ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ K)
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (2 ^ K)) n : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro n hnmem
          rw [Finset.mem_Icc] at hnmem
          exact_mod_cast card_divisors_pow_le_zeta_pow K n (by omega)
    _ = (generalizedDivisorNatSum (2 ^ K) N : ℝ) := by
          rw [generalizedDivisorNatSum, Nat.cast_sum]
    _ ≤ (N : ℝ) * (((harmonic N : ℚ) : ℝ) ^ (2 ^ K - 1)) := by
          simpa only [hpow] using
            generalizedDivisorNatSum_cast_le_harmonic (2 ^ K - 1) N hN
    _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hhar0 (harmonic_le_one_add_log N) (2 ^ K - 1))
            (by positivity)

/-- Reindex a sum on anchored positive integers as a sum over `Fin N`. -/
theorem sum_fin_add_one_eq_sum_Icc {R : Type*} [AddCommMonoid R]
    (N : ℕ) (f : ℕ → R) :
    ∑ j : Fin N, f ((j : ℕ) + 1) = ∑ n ∈ Finset.Icc 1 N, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => f (j + 1)) N]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

/-- `Fin N` form of the fixed divisor-moment estimate, matching coefficient-vector indexing. -/
theorem sum_fin_card_divisors_pow_le_polylog (K N : ℕ) (hN : 1 ≤ N) :
    ∑ j : Fin N, (((j : ℕ) + 1).divisors.card : ℝ) ^ K ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by
  rw [sum_fin_add_one_eq_sum_Icc N
    (fun n => ((n.divisors.card : ℝ) ^ K))]
  exact sum_card_divisors_pow_le_polylog K N hN

end RHTower.Sieve
