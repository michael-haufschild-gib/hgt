import GaloisForLFunctions.RHTower.Sieve.FreeScaleWindowCount
import GaloisForLFunctions.RHTower.Sieve.MertensWindowSharp
import GaloisForLFunctions.RHTower.Sieve.MarkerCountUpper

/-!
# The harmonic mass and the count of a free-scale marker range

The marker range of a free-scale construction is `(X/m, X/(m/2^{K₀+1})]`, whose top is at least
`2^{K₀+1}` times its bottom.  So the sharp Mertens estimate and Brun–Titchmarsh apply to it exactly
as they do to a dyadic tower of `K₀+1` blocks at a fixed base.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- **The marker range spans a factor `2^{K₀+1}`.** -/
theorem freeRange_top_ge {X m K₀ : ℕ} (hdvd : 2 ^ (K₀ + 1) ∣ m) :
    2 ^ (K₀ + 1) * (X / freeStart m 0) ≤ X / freeStart m (K₀ + 1) := by
  obtain ⟨d, rfl⟩ := hdvd
  have h0 : freeStart (2 ^ (K₀ + 1) * d) 0 = 2 ^ (K₀ + 1) * d :=
    freeStart_pow_mul (by omega)
  have h1 : freeStart (2 ^ (K₀ + 1) * d) (K₀ + 1) = d := by
    rw [freeStart_pow_mul (le_refl _)]
    simp
  rw [h0, h1]
  have hsplit : X / (2 ^ (K₀ + 1) * d) = X / d / 2 ^ (K₀ + 1) := by
    rw [Nat.div_div_eq_div_mul, mul_comm]
  rw [hsplit, mul_comm]
  exact Nat.div_mul_le_self _ _

/-- **The harmonic mass of a free-scale marker range, from below.** -/
theorem free_harm_ge {X m K₀ : ℕ} (hdvd : 2 ^ (K₀ + 1) ∣ m)
    (hz : 2 ≤ X / freeStart m 0) :
    logLog (X / freeStart m (K₀ + 1)) - logLog (X / freeStart m 0)
        - ((2 * mertensFirstConst + 1 / 2)
              / Real.log ((X / freeStart m (K₀ + 1) : ℕ) : ℝ)
          + (2 * mertensFirstConst + 1 / 2) / Real.log ((X / freeStart m 0 : ℕ) : ℝ))
      ≤ ∑ p ∈ freeRange X m K₀, 1 / (p : ℝ) := by
  rw [freeRange]
  have htop := freeRange_top_ge (X := X) (m := m) (K₀ := K₀) hdvd
  have hzb : X / freeStart m 0 ≤ X / freeStart m (K₀ + 1) := by
    have hp1 : 1 ≤ 2 ^ (K₀ + 1) := Nat.one_le_two_pow
    nlinarith [htop, hp1]
  exact sum_inv_bigPrimeSet_ge_sharp hz hzb

/-- **The logarithm of the top of a free-scale marker range.** -/
theorem log_freeRange_top_ge {X m K₀ : ℕ} (hdvd : 2 ^ (K₀ + 1) ∣ m)
    (hz : 2 ≤ X / freeStart m 0) :
    ((K₀ : ℝ) + 1) * Real.log 2 + Real.log ((X / freeStart m 0 : ℕ) : ℝ)
      ≤ Real.log ((X / freeStart m (K₀ + 1) : ℕ) : ℝ) := by
  have htop := freeRange_top_ge (X := X) (m := m) (K₀ := K₀) hdvd
  have hzR : (2 : ℝ) ≤ ((X / freeStart m 0 : ℕ) : ℝ) := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < ((X / freeStart m 0 : ℕ) : ℝ) := by linarith
  have htopR : (2 : ℝ) ^ (K₀ + 1) * ((X / freeStart m 0 : ℕ) : ℝ)
      ≤ ((X / freeStart m (K₀ + 1) : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 htop
    push_cast at this
    exact this
  have hmono := Real.log_le_log (by positivity) htopR
  rw [Real.log_mul (by positivity) (ne_of_gt hz0), Real.log_pow] at hmono
  push_cast at hmono
  linarith

/-- **The count of a free-scale marker range, from above.** -/
theorem free_count_le {X m K₀ Y : ℕ} (hY : 1 ≤ Y) (hYM : Y ≤ X / freeStart m 0)
    (hM : 2 ≤ X / freeStart m 0) (hdvd : 2 ^ (K₀ + 1) ∣ m) (hlog : 0 < Real.log Y) :
    (((freeRange X m K₀).card : ℕ) : ℝ)
      ≤ 2 * (((X / freeStart m (K₀ + 1) : ℕ) : ℝ) - ((X / freeStart m 0 : ℕ) : ℝ))
          / Real.log ((Y : ℕ) : ℝ)
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst)
              * (Real.log ((X / freeStart m 0 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
  rw [freeRange]
  have htop := freeRange_top_ge (X := X) (m := m) (K₀ := K₀) hdvd
  have hzb : X / freeStart m 0 ≤ X / freeStart m (K₀ + 1) := by
    have hp1 : 1 ≤ 2 ^ (K₀ + 1) := Nat.one_le_two_pow
    nlinarith [htop, hp1]
  exact card_bigPrimeSet_le_explicit hzb hY hYM hM hlog

end

end RHTower.Sieve
