import GaloisForLFunctions.RHTower.Sieve.PrimeLogSqLower
import GaloisForLFunctions.RHTower.Sieve.HalaszDichotomy

/-!
# The frequency window is `O(δ / log N)`

Substituting the explicit weight bound `∑_{p ≤ N}(log p)²/p ≥ ½log²N - 39 log N - 25` into the
separation inequality `(t-u)² ∑_{p ∈ P}(log p)²/p ≤ 2π²δ²` gives

`(t-u)² (½log²N - 39 log N - 25) ≤ 2π²δ²`,

so once the weight is positive the two frequencies satisfy `|t - u| = O(δ / log N)`.

Every constant is explicit and the input is Mertens-level: no prime number theorem, no zero-free
region.  A lower bound on `δ` itself is where the analysis enters; for the Möbius function
`MoebiusUniformFrequency.lean` proves one, uniformly over a frequency range.
-/

namespace RHTower.Sieve

open Finset

/-- The weight appearing in the frequency window. -/
noncomputable def logSqWeight (N : ℕ) : ℝ := Real.log N ^ (2 : ℕ) / 2 - 39 * Real.log N - 25

/-- **The frequency window, in squared form.** -/
theorem sq_sub_mul_logSqWeight_le {f : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hf : ∀ p ∈ Nat.primesLE N, ‖f p‖ ≤ 1) {t u δ : ℝ}
    (ht : Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE N)) ≤ δ)
    (hu : Real.sqrt (mulDistSqPair f (charFn u) (Nat.primesLE N)) ≤ δ)
    (hsmall : ∀ p ∈ Nat.primesLE N, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi) :
    (t - u) ^ (2 : ℕ) * logSqWeight N ≤ 2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) := by
  have hP : ∀ p ∈ Nat.primesLE N, 0 < p := fun p hp => (Nat.prime_of_mem_primesLE hp).pos
  have hbase := sq_mul_sum_sq_log_le_of_close hf hP ht hu hsmall
  have hW : logSqWeight N ≤ ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) ^ (2 : ℕ) / (p : ℝ) :=
    sum_prime_log_sq_div_ge N hN
  have hstep : (t - u) ^ (2 : ℕ) * logSqWeight N
      ≤ (t - u) ^ (2 : ℕ) * ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) ^ (2 : ℕ) / (p : ℝ) :=
    mul_le_mul_of_nonneg_left hW (sq_nonneg _)
  linarith

/-- **The frequency window.**  Once the weight is positive, `|t - u|² ≤ 2π²δ²/W`. -/
theorem sq_sub_le_div {f : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hf : ∀ p ∈ Nat.primesLE N, ‖f p‖ ≤ 1) {t u δ : ℝ} (hW : 0 < logSqWeight N)
    (ht : Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE N)) ≤ δ)
    (hu : Real.sqrt (mulDistSqPair f (charFn u) (Nat.primesLE N)) ≤ δ)
    (hsmall : ∀ p ∈ Nat.primesLE N, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi) :
    (t - u) ^ (2 : ℕ) ≤ 2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight N := by
  rw [le_div_iff₀ hW]
  exact sq_sub_mul_logSqWeight_le hN hf ht hu hsmall

end RHTower.Sieve
