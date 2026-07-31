import GaloisForLFunctions.RHTower.DirichletLMixedAdditiveZeroAbscissaLaw
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The Mertens integration law

Replacing a coefficient sequence by its partial sums multiplies the generating series by
`(1 - X)⁻¹`.  A Hermitian mixed `2k`-fold convolution therefore acquires the factor `(1 - X)^{-2k}`,
whose coefficients are the binomial numbers, giving the exact finite identity

```
C_k(N) = ∑_{i+j=N} R_k(i) · binom(2k-1+j, 2k-1),
```

where `R_k` is built from the coefficients and `C_k` from their partial sums.  This is the exact
integration law relating the raw Hermitian convolution to the Mertens-type one.
-/

open Complex PowerSeries
open scoped BigOperators

namespace RHTower

/-- The sequence of partial sums. -/
noncomputable def partialSumSeq (a : ℕ → ℂ) : ℕ → ℂ := fun N => ∑ n ∈ Finset.range (N + 1), a n

/-- Passing to partial sums multiplies the generating series by `1 + X + X² + ⋯`. -/
theorem mk_partialSumSeq (a : ℕ → ℂ) :
    PowerSeries.mk (partialSumSeq a) = PowerSeries.mk a * PowerSeries.mk (1 : ℕ → ℂ) := by
  ext N
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, partialSumSeq,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => a i)]
  exact Finset.sum_congr rfl fun ij _ => by simp

/-- Conjugation commutes with partial summation. -/
theorem conj_partialSumSeq (a : ℕ → ℂ) :
    (fun n => (starRingEnd ℂ) (partialSumSeq a n)) = partialSumSeq fun n => (starRingEnd ℂ) (a n) := by
  funext N
  rw [partialSumSeq, partialSumSeq, map_sum]

/-- Conjugation commutes with the additive convolution power. -/
theorem conj_additiveConvolutionPower (a : ℕ → ℂ) (k N : ℕ) :
    (starRingEnd ℂ) (additiveConvolutionPower a k N) =
      additiveConvolutionPower (fun n => (starRingEnd ℂ) (a n)) k N := by
  induction k generalizing N with
  | zero => simp [additiveConvolutionPower]
  | succ k ih =>
      rw [additiveConvolutionPower, additiveConvolutionPower, map_sum]
      exact Finset.sum_congr rfl fun pq _ => by rw [map_mul, ih pq.1]

/-- The Hermitian mixed convolution power is a coefficient of the product of the `k`-th powers of
the generating series and its conjugate. -/
theorem mixedAdditiveConvolutionPower_eq_coeff (a : ℕ → ℂ) (k N : ℕ) :
    mixedAdditiveConvolutionPower a k N =
      (PowerSeries.coeff (R := ℂ) N)
        ((PowerSeries.mk a) ^ k * (PowerSeries.mk fun n => (starRingEnd ℂ) (a n)) ^ k) := by
  rw [mixedAdditiveConvolutionPower, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [← additiveConvolutionPower_eq_coeff_pow, ← additiveConvolutionPower_eq_coeff_pow]
  congr 1
  exact conj_additiveConvolutionPower a k ij.2

/-- **The Mertens integration law.**  Passing from a coefficient sequence to its partial sums
multiplies the Hermitian mixed `2(k+1)`-fold convolution by the binomial kernel of
`(1 - X)^{-(2k+2)}`. -/
theorem mixedAdditiveConvolutionPower_partialSumSeq (a : ℕ → ℂ) (k N : ℕ) :
    mixedAdditiveConvolutionPower (partialSumSeq a) (k + 1) N =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
        mixedAdditiveConvolutionPower a (k + 1) ij.1 *
          ((Nat.choose (2 * k + 1 + ij.2) (2 * k + 1) : ℂ)) := by
  have hconj : (PowerSeries.mk fun n => (starRingEnd ℂ) (partialSumSeq a n)) =
      (PowerSeries.mk fun n => (starRingEnd ℂ) (a n)) * PowerSeries.mk (1 : ℕ → ℂ) := by
    rw [conj_partialSumSeq, mk_partialSumSeq]
  have hsplit :
      (PowerSeries.mk (partialSumSeq a)) ^ (k + 1) *
          (PowerSeries.mk fun n => (starRingEnd ℂ) (partialSumSeq a n)) ^ (k + 1) =
        ((PowerSeries.mk a) ^ (k + 1) *
            (PowerSeries.mk fun n => (starRingEnd ℂ) (a n)) ^ (k + 1)) *
          (PowerSeries.mk (1 : ℕ → ℂ)) ^ (2 * k + 2) := by
    rw [mk_partialSumSeq, hconj, mul_pow, mul_pow,
      show 2 * k + 2 = (k + 1) + (k + 1) by ring, pow_add]
    ring
  rw [mixedAdditiveConvolutionPower_eq_coeff, hsplit, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [← mixedAdditiveConvolutionPower_eq_coeff]
  congr 1
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, PowerSeries.mk_one_pow_eq_mk_choose_add,
    PowerSeries.coeff_mk]

/-- The integration law in explicit range form: `C_k(N) = ∑_{j ≤ N} binom(N-j+2k+1, 2k+1) R_k(j)`. -/
theorem mixedAdditiveConvolutionPower_partialSumSeq_range (a : ℕ → ℂ) (k N : ℕ) :
    mixedAdditiveConvolutionPower (partialSumSeq a) (k + 1) N =
      ∑ j ∈ Finset.range (N + 1),
        mixedAdditiveConvolutionPower a (k + 1) j *
          ((Nat.choose (2 * k + 1 + (N - j)) (2 * k + 1) : ℂ)) := by
  rw [mixedAdditiveConvolutionPower_partialSumSeq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Partial sums of a real sequence are real. -/
theorem partialSumSeq_im_eq_zero {a : ℕ → ℂ} (ha : ∀ N, (a N).im = 0) (N : ℕ) :
    (partialSumSeq a N).im = 0 := by
  rw [partialSumSeq, Complex.im_sum]
  exact Finset.sum_eq_zero fun n _ => ha n

/-- **The integration law for the even convolution power.**  On a real coefficient sequence the
Hermitian mixed law is the plain `2k`-fold even additive convolution, so the same binomial kernel
relates the even convolution of the partial sums to that of the coefficients. -/
theorem additiveConvolutionPower_partialSumSeq_of_real {a : ℕ → ℂ}
    (ha : ∀ N, (a N).im = 0) (k N : ℕ) :
    additiveConvolutionPower (partialSumSeq a) (2 * (k + 1)) N =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
        additiveConvolutionPower a (2 * (k + 1)) ij.1 *
          ((Nat.choose (2 * k + 1 + ij.2) (2 * k + 1) : ℂ)) := by
  rw [← mixedAdditiveConvolutionPower_eq_additiveConvolutionPower_two_mul_of_real
      (partialSumSeq a) (partialSumSeq_im_eq_zero ha) (k + 1) N,
    mixedAdditiveConvolutionPower_partialSumSeq]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [mixedAdditiveConvolutionPower_eq_additiveConvolutionPower_two_mul_of_real a ha (k + 1) ij.1]

end RHTower
