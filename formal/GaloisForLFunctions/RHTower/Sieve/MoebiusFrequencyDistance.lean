import GaloisForLFunctions.RHTower.Sieve.MoebiusDistance
import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum

/-!
# The Möbius function is far from every character

Combining the elementary identity `D(μ, χ_t; p ≤ z)² = ∑_{p ≤ z}(1 + cos(t log p))/p` with Mertens'
second theorem and the prime cosine bound gives a lower bound valid at *every* frequency, not just
at `t = 0`.

The truncation is tied to the frequency by `log⁹|t|/A ≤ log z`, which is what the zero-free strip
demands.  That coupling is a gain rather than a cost: it forces `log log z ≥ 9 log log|t| − log A`,
while the strip loses only `7 log log|t|`, so

    D(μ, χ_t; p ≤ z)²  ≥  2 log log|t| − C

with `C` absolute.  The distance therefore grows with the frequency, and Halász's dichotomy has no
exceptional character to avoid in this range.
-/

namespace RHTower.Sieve

open Finset RHTower

/-- The absolute constant in the frequency-uniform Möbius distance bound. -/
noncomputable def moebiusFrequencyConst : ℝ :=
  mertensSecondLowerConst + Real.log zetaLowerA + Real.log (20 / zetaLowerA)
    + Real.pi ^ (2 : ℕ) / 6 + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    + 1 + Real.log 4

/-- The squared distance splits into Mertens' sum and the cosine sum. -/
theorem mulDistSqPair_neg_one_split {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, f p = -1)
    (t : ℝ) :
    mulDistSqPair f (charFn t) P
      = (∑ p ∈ P, 1 / (p : ℝ)) + ∑ p ∈ P, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ) := by
  rw [mulDistSqPair_neg_one_charFn hf t, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- The truncation forced by the strip pushes `log log z` above `9 log log|t|`. -/
theorem nine_mul_logLog_le_logLog {z : ℕ} {t : ℝ} (hz : 3 ≤ z) (ht : 9 ≤ |t|)
    (hzt : 1 / Real.log z ≤ zetaLowerA / Real.log |t| ^ (9 : ℕ)) :
    9 * Real.log (Real.log |t|) - Real.log zetaLowerA ≤ logLog z := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlogt : (0 : ℝ) < Real.log |t| := Real.log_pos (by linarith)
  have hpow : (0 : ℝ) < Real.log |t| ^ (9 : ℕ) := by positivity
  rw [div_le_div_iff₀ hlogz0 hpow] at hzt
  have hle : Real.log |t| ^ (9 : ℕ) / zetaLowerA ≤ Real.log (z : ℝ) := by
    rw [div_le_iff₀ hA0]
    nlinarith
  have hlog := Real.log_le_log (by positivity) hle
  have hval : Real.log (Real.log |t| ^ (9 : ℕ) / zetaLowerA)
      = 9 * Real.log (Real.log |t|) - Real.log zetaLowerA := by
    rw [Real.log_div (by positivity) (ne_of_gt hA0), Real.log_pow]
    push_cast
    ring
  rw [hval] at hlog
  rw [logLog]
  exact hlog

/-- The strip loss splits off its `7 log log|t|`. -/
theorem log_strip_bound_eq {t : ℝ} (ht : 9 ≤ |t|) :
    Real.log (20 / zetaLowerA * Real.log |t| ^ (7 : ℕ))
      = Real.log (20 / zetaLowerA) + 7 * Real.log (Real.log |t|) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlogt : (0 : ℝ) < Real.log |t| := Real.log_pos (by linarith)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

/-- **The Möbius function is far from every character.**  Unconditional, and the lower bound grows
with the frequency. -/
theorem two_mul_logLog_abs_sub_le_mulDistSqPair {f : ℕ → ℂ} {z : ℕ} {t : ℝ}
    (hz : 3 ≤ z) (ht : 9 ≤ |t|)
    (hzt : 1 / Real.log z ≤ zetaLowerA / Real.log |t| ^ (9 : ℕ))
    (hf : ∀ p ∈ Nat.primesLE z, f p = -1) :
    2 * Real.log (Real.log |t|) - moebiusFrequencyConst
      ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  have hmertens : logLog z - mertensSecondLowerConst ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
    le_mertensS (by omega)
  have hcos := sum_cos_div_prime_ge hz ht hzt
  have hlow := nine_mul_logLog_le_logLog hz ht hzt
  have hstrip := log_strip_bound_eq ht
  rw [mulDistSqPair_neg_one_split hf t, moebiusFrequencyConst]
  rw [hstrip] at hcos
  linarith

end RHTower.Sieve
