import GaloisForLFunctions.RHTower.Sieve.FejerSymmetric

/-!
# The two properties of the Fejér transform

`(2 - 2 cos TL)/(TL²)` is nonnegative, at most `4/(TL²)`, and at most `T`.

The first two are immediate from `-1 ≤ cos ≤ 1`.  The third is the quadratic bound
`1 - θ²/2 ≤ cos θ` at `θ = TL`, which caps the transform near the trivial frequency exactly as the
sharp kernel's `2T` does.

Together they are what a localisation argument cites: the transform is a nonnegative weight of total
size `T` concentrated on `|L| ≲ T^{-1}`, with a square-summable tail.
-/

namespace RHTower.Sieve

/-- **The Fejér transform is nonnegative.** -/
theorem fejer_transform_nonneg (L : ℝ) {T : ℝ} (hT : 0 < T) :
    (0 : ℝ) ≤ (2 - 2 * Real.cos (T * L)) / (T * L ^ (2 : ℕ)) := by
  have hnum : (0 : ℝ) ≤ 2 - 2 * Real.cos (T * L) := by
    have := Real.cos_le_one (T * L)
    linarith
  have hden : (0 : ℝ) ≤ T * L ^ (2 : ℕ) := by positivity
  positivity

/-- **The Fejér transform decays in the frequency.** -/
theorem fejer_transform_le_inv (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    (2 - 2 * Real.cos (T * L)) / (T * L ^ (2 : ℕ)) ≤ 4 / (T * L ^ (2 : ℕ)) := by
  have hden : (0 : ℝ) < T * L ^ (2 : ℕ) := by
    have hL2 : (0 : ℝ) < L ^ (2 : ℕ) := by positivity
    positivity
  have hnum : 2 - 2 * Real.cos (T * L) ≤ 4 := by
    have := Real.neg_one_le_cos (T * L)
    linarith
  gcongr

/-- **The Fejér transform is capped by the interval length.** -/
theorem fejer_transform_le_len (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    (2 - 2 * Real.cos (T * L)) / (T * L ^ (2 : ℕ)) ≤ T := by
  have hden : (0 : ℝ) < T * L ^ (2 : ℕ) := by
    have hL2 : (0 : ℝ) < L ^ (2 : ℕ) := by positivity
    positivity
  rw [div_le_iff₀ hden]
  have hquad : 1 - (T * L) ^ (2 : ℕ) / 2 ≤ Real.cos (T * L) :=
    Real.one_sub_sq_div_two_le_cos
  nlinarith [hquad]

end RHTower.Sieve
