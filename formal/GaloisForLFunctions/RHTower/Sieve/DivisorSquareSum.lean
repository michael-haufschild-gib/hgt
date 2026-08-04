import GaloisForLFunctions.RHTower.Sieve.BrunTitchmarsh
import GaloisForLFunctions.RHTower.Sieve.RoughCount

/-!
# The divisor-square error sum

A squarefree number has `2^{ω d}` divisors, so the `Λ²` coefficient bound `|Λ²_d| ≤ τ(d)²` reads
`|Λ²_d| ≤ 4^{ω d}`.  Summing that over the divisors of `z#` below the level `D` costs only a power
of `log z`:

`∑_{d ∣ z#, d ≤ D} 4^{ω d} ≤ D · ∏_{p ≤ z} (1 + 4/p)`,

because `d ≤ D` lets each term be weighted by `D/d`, after which the sum is the tilted Euler
product already computed in `TruncationDefect.lean`.

Combined with the support statement `Λ²_d = 0` for `d > Y²`, the whole Selberg error of an interval
sieve is at most `Y² ∏_{p ≤ z}(1 + 4/p)`.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- A squarefree number has `2^{ω}` divisors. -/
private theorem card_divisors_of_squarefree {d : ℕ} (hd : Squarefree d) :
    d.divisors.card = 2 ^ d.primeFactors.card := by
  classical
  have h := sum_divisors_eq_sum_powerset hd (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powerset] at h
  exact h

/-- The `Λ²` coefficients of a squarefree modulus are bounded by `4^{ω d}`. -/
theorem abs_lambdaSquared_le_four_pow {w : ℕ → ℝ} (hw : ∀ n, |w n| ≤ 1) {d : ℕ}
    (hd : Squarefree d) :
    |lambdaSquared w d| ≤ (4 : ℝ) ^ d.primeFactors.card := by
  refine le_trans (abs_lambdaSquared_le_card_sq hw d) ?_
  rw [card_divisors_of_squarefree hd]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **Level-restricted divisor-square sum.** -/
theorem sum_four_pow_le (z D : ℕ) :
    ∑ d ∈ {d ∈ (primorial z).divisors | d ≤ D}, (4 : ℝ) ^ d.primeFactors.card
      ≤ (D : ℝ) * ∏ p ∈ Nat.primesLE z, (1 + 4 / (p : ℝ)) := by
  classical
  have hstep : ∀ d ∈ {d ∈ (primorial z).divisors | d ≤ D},
      (4 : ℝ) ^ d.primeFactors.card ≤ (D : ℝ) * ((4 : ℝ) ^ d.primeFactors.card / d) := by
    intro d hd
    obtain ⟨hdmem, hdD⟩ := Finset.mem_filter.1 hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hDR : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
    have hpow : (0 : ℝ) < (4 : ℝ) ^ d.primeFactors.card := by positivity
    rw [mul_div_assoc']
    rw [le_div_iff₀ hdR]
    nlinarith [hpow, hDR, hdR]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  refine mul_le_mul_of_nonneg_left ?_ hDnn
  have hfull := sum_divisors_pow_card_primeFactors_div_eq_prod
    (squarefree_primorial z) (4 : ℝ)
  rw [primeFactors_primorial_eq] at hfull
  rw [← hfull]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro d hd _
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  positivity

/-- **Selberg error of an interval sieve.**  The whole error is at most the level times a fixed
power of the Euler product. -/
theorem sum_abs_lambdaSquared_le (a b z Y : ℕ) (hY : 1 ≤ Y) :
    ∑ d ∈ (primorial z).divisors,
        |lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y) d|
      ≤ ((Y * Y : ℕ) : ℝ) * ∏ p ∈ Nat.primesLE z, (1 + 4 / (p : ℝ)) := by
  classical
  have hzero : ∀ d ∈ (primorial z).divisors, d ∉ {d ∈ (primorial z).divisors | d ≤ Y * Y} →
      |lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y) d| = 0 := by
    intro d hd hnot
    have hlt : Y * Y < d := by
      by_contra hcon
      exact hnot (Finset.mem_filter.2 ⟨hd, by omega⟩)
    rw [lambdaSquared_selbergTruncWeight_eq_zero (intervalSieve a b z) hlt, abs_zero]
  rw [← Finset.sum_subset (Finset.filter_subset (fun d => d ≤ Y * Y) (primorial z).divisors) hzero]
  refine le_trans (Finset.sum_le_sum ?_) (sum_four_pow_le z (Y * Y))
  intro d hd
  obtain ⟨hdmem, -⟩ := Finset.mem_filter.1 hd
  have hdsq : Squarefree d :=
    (squarefree_primorial z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hdmem)
  refine abs_lambdaSquared_le_four_pow ?_ hdsq
  intro n
  by_cases hn : n ∣ primorial z
  · exact abs_selbergTruncWeight_le_one (intervalSieve a b z) hn hY
  · have hz : selbergTruncWeight (intervalSieve a b z) Y n = 0 := by
      unfold selbergTruncWeight selbergW
      have hnum : ∀ l ∈ (intervalSieve a b z).prodPrimes.divisors,
          (if n ∣ l then (ArithmeticFunction.moebius (l / n) : ℝ)
              * selbergTruncY (intervalSieve a b z) Y l else 0) = 0 := by
        intro l hl
        by_cases hnl : n ∣ l
        · rw [intervalSieve_prodPrimes] at hl
          exact absurd (hnl.trans (Nat.dvd_of_mem_divisors hl)) hn
        · rw [if_neg hnl]
      rw [Finset.sum_congr rfl hnum, Finset.sum_const_zero, zero_div]
    rw [hz, abs_zero]
    norm_num

/-- **Brun–Titchmarsh, fully explicit.**  Every quantity is an elementary function of the
parameters: the main term is `2(b−a)/log Y`, and the error is the level `Y²` times a fourth power
of `log z`. -/
theorem card_coprime_Ioc_le_explicit (a b z Y : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    ((#{n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ)) := by
  have hmain := card_coprime_Ioc_le_log a b z Y hab hY hYz hlog
  have herr := sum_abs_lambdaSquared_le a b z Y hY
  have heuler : ∏ p ∈ Nat.primesLE z, (1 + 4 / (p : ℝ))
      ≤ Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ) :=
    prod_one_add_primesLE_le hz (by norm_num)
  have hYnn : (0 : ℝ) ≤ ((Y * Y : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left heuler hYnn
  linarith

end RHTower.Sieve
