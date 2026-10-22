import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitShortenedCutoffWindow

/-!
# A cubic bound for shortening the square-root cutoff

At radius `(m+k)^2`, retaining only Möbius coefficients through `m`
changes the actual reconstruction by at most `27 k^3/m`, provided
`m > 0` and `3k <= m`. When `k^3 <= m^2`, this entire signed defect is
already at square-root scale. The retained action is still unbounded here.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

/-- The complete signed defect is supported on a square of exactly `3k`
indices per side; all other interactions vanish by causality. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_strip
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) :
    ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ)) -
      ccmPrimeDeficitTruncatedAction m (2 * Real.log (m + k : ℕ)) =
        ∑ a ∈ Finset.Icc (m + 1) (m + 3 * k), ∑ b ∈ Finset.Icc (m + 1) (m + 3 * k),
          logarithmicLongTail m moebiusCoeff a * logarithmicLongTail m moebiusCoeff b *
            ccmPrimeDeficitDivisorSource (2 * Real.log (m + k : ℕ) - Real.log (a * b : ℕ)) := by
  exact ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_eq_strip hm hk
    (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)) le_rfl

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_cubic_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) :
    |ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ)) -
      ccmPrimeDeficitTruncatedAction m (2 * Real.log (m + k : ℕ))| ≤
        27 * (k : ℝ) ^ 3 / m := by
  exact abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_cubic_le hm hk
    (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)) le_rfl

/-- A width with cube at most `m^2` costs at most `27m`, hence at most
`27 sqrt(x)` at the terminal radius `x=(m+k)^2`. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_critical_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (hc : k ^ 3 ≤ m ^ 2) :
    |ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ)) -
      ccmPrimeDeficitTruncatedAction m (2 * Real.log (m + k : ℕ))| ≤ 27 * (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcR : (k : ℝ) ^ 3 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hc
  calc
    _ ≤ 27 * (k : ℝ) ^ 3 / m :=
      abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_cubic_le hm hk
    _ ≤ 27 * (m : ℝ) ^ 2 / m := by gcongr
    _ = _ := by field_simp

/-- An unconditional infinite family: the omitted width is `(r+3)^2`,
while the retained cutoff is `(r+3)^3`. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_sub_cubicCutoff_le (r : ℕ) :
    |ccmLogChebyshevDeficitPrimitive (2 * Real.log ((r + 3) ^ 3 + (r + 3) ^ 2 : ℕ)) -
      ccmPrimeDeficitTruncatedAction ((r + 3) ^ 3)
        (2 * Real.log ((r + 3) ^ 3 + (r + 3) ^ 2 : ℕ))| ≤
          27 * ((r + 3 : ℕ) : ℝ) ^ 3 := by
  have hm : 0 < (r + 3) ^ 3 := by positivity
  have hk : 3 * (r + 3) ^ 2 ≤ (r + 3) ^ 3 := by
    calc
      _ ≤ (r + 3) * (r + 3) ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hc : ((r + 3) ^ 2) ^ 3 ≤ ((r + 3) ^ 3) ^ 2 := le_of_eq (by ring)
  simpa only [Nat.cast_pow] using
    abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_critical_le hm hk hc

end RHTower
