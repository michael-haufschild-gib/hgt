import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# The harmonic mass of a wide prime range

`Sieve/PrimeRangeMertensMass.sum_inv_primesRange_le` bounds the mass of a range by
`(log z − log z₀ + 2c)/log z₀`, which is sharp for a *narrow* band and useless for a wide one.  For
a range whose two ends have logarithms of different orders the right bound is the difference of the
Mertens logarithms: because `Sieve/MertensSecondSharp` carries a **decaying** error, the two
Meissel–Mertens constants cancel exactly and only `O(1/log z₀)` survives.

This is what turns a range `(log x)^K < p ≤ exp((log x)^β)` into harmonic mass `≍ β·log log x`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The harmonic mass of a wide prime range.** -/
theorem sum_inv_primesRange_le_logLog_diff {z₀ z : ℕ} (h₀ : 2 ≤ z₀) (hz : z₀ ≤ z) :
    ∑ p ∈ primesRange z₀ z, 1 / (p : ℝ)
      ≤ Real.log (Real.log z) - Real.log (Real.log z₀)
        + 2 * ((2 * mertensFirstConst + 1 / 2) / Real.log z₀) := by
  have hz2 : 2 ≤ z := le_trans h₀ hz
  have hlog₀ : (0 : ℝ) < Real.log z₀ := by
    have h2 : (2 : ℝ) ≤ (z₀ : ℝ) := by exact_mod_cast h₀
    exact Real.log_pos (by linarith)
  have hlogz : (0 : ℝ) < Real.log z := by
    have h2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
    exact Real.log_pos (by linarith)
  have hz₀0 : (0 : ℝ) < ((z₀ : ℕ) : ℝ) := by
    have : 0 < z₀ := by omega
    exact_mod_cast this
  have hmono : Real.log z₀ ≤ Real.log z := by
    have hle : ((z₀ : ℕ) : ℝ) ≤ ((z : ℕ) : ℝ) := by exact_mod_cast hz
    exact Real.log_le_log hz₀0 hle
  have hA := abs_mertensS_sub_logLog_sub_const_le hz2
  have hB := abs_mertensS_sub_logLog_sub_const_le h₀
  have hA' : mertensS z - logLog z - meisselMertensConst
      ≤ (2 * mertensFirstConst + 1 / 2) / Real.log z := (abs_le.1 hA).2
  have hB' : -((2 * mertensFirstConst + 1 / 2) / Real.log z₀)
      ≤ mertensS z₀ - logLog z₀ - meisselMertensConst := (abs_le.1 hB).1
  have herr : (2 * mertensFirstConst + 1 / 2) / Real.log z
      ≤ (2 * mertensFirstConst + 1 / 2) / Real.log z₀ := by
    have hc0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    exact div_le_div_of_nonneg_left hc0 hlog₀ hmono
  rw [sum_inv_primesRange hz]
  simp only [logLog] at hA' hB'
  linarith

end

end RHTower.Sieve
