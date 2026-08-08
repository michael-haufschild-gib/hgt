import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# Mertens' first theorem on a dyadic block

Differencing the two-sided Mertens first theorem at consecutive powers of two bounds the mass of a
dyadic block of primes by an absolute constant:

`∑_{2^k < p ≤ 2^{k+1}} (log p)/p ≤ log 2 + log 4 + 1 + 2·logSqTailConst`,

independently of `k`.  The upper bound at `2^{k+1}` contributes `(k+1)log 2 + log 4` and the lower bound
at `2^k` removes `k log 2 − 1 − 2·logSqTailConst`, so the `k log 2` cancels and only the increment
survives.

This is the per-block input that a dyadic decomposition of a prime sum needs.  In particular
`1/(p log p) ≤ ((log p)/p)/(k log 2)²` on the `k`-th block, so the block bound converts
`∑_p 1/(p log p)` into `∑_k 1/k²` — the missing ingredient for making the frequency-average error of
`UniformDistanceAverage` absolute rather than `O(logLog z/T)`.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The absolute bound for the mass of one dyadic block of primes. -/
noncomputable def mertensBlockConst : ℝ :=
  Real.log 2 + Real.log 4 + 1 + 2 * logSqTailConst

theorem mertensBlockConst_nonneg : 0 ≤ mertensBlockConst := by
  rw [mertensBlockConst]
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hL := logSqTailConst_nonneg
  linarith

/-- **Mertens' first theorem on a dyadic block.**  The mass of the primes in `(2^k, 2^{k+1}]` is at
most an absolute constant, uniformly in `k`. -/
theorem sum_prime_log_div_block_le (k : ℕ) :
    ∑ p ∈ Nat.primesLE (2 ^ (k + 1)) \ Nat.primesLE (2 ^ k), Real.log (p : ℝ) / (p : ℝ)
      ≤ mertensBlockConst := by
  classical
  have hsub : Nat.primesLE (2 ^ k) ⊆ Nat.primesLE (2 ^ (k + 1)) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    refine ⟨le_trans hp.1 ?_, hp.2⟩
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hone : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have hone' : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hup := mertensFirst_upper hone'
  have hlow := mertensFirst_lower hone
  have hcast : Real.log ((2 ^ (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    rfl
  have hcast' : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hcast] at hup
  rw [hcast'] at hlow
  rw [Finset.sum_sdiff_eq_sub hsub, mertensBlockConst]
  linarith

end RHTower.Sieve
end
