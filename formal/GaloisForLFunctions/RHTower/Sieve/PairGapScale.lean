import GaloisForLFunctions.RHTower.Sieve.EffectiveShortRange

/-!
# The curvature scale of an off-diagonal pair

For a pair `(m₁, m₂)` of short values the difference of offsets is `r·h/(m₁m₂)` with
`h = |m₂ − m₁|`, so the correlation's curvature scale is `Y = T r h/(m₁m₂)`.  Confining the pair to
the effective range turns this into a two-sided bound in terms of `h` alone, which is what the
`h`-sum consumes.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The offset gap of a pair.** -/
theorem abs_inv_diff {r : ℝ} (hr : 0 ≤ r) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    |r / m₁ - r / m₂| = r * |(m₂ : ℝ) - (m₁ : ℝ)| / ((m₁ : ℝ) * (m₂ : ℝ)) := by
  have h1 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have h2 : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂
  have hid : r / (m₁ : ℝ) - r / (m₂ : ℝ)
      = r * ((m₂ : ℝ) - (m₁ : ℝ)) / ((m₁ : ℝ) * (m₂ : ℝ)) := by
    field_simp
  rw [hid, abs_div, abs_mul, abs_of_nonneg hr,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m₁ : ℝ) * (m₂ : ℝ))]

/-- The gap scale from below, when the pair is confined to `[M₀, M₁]`. -/
theorem le_abs_inv_diff {r : ℝ} (hr : 0 ≤ r) {m₁ m₂ M₁ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (h1 : m₁ ≤ M₁) (h2 : m₂ ≤ M₁) :
    r * |(m₂ : ℝ) - (m₁ : ℝ)| / ((M₁ : ℝ) * (M₁ : ℝ)) ≤ |r / m₁ - r / m₂| := by
  have hp1 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have hp2 : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂
  have hM : (0 : ℝ) < (M₁ : ℝ) := lt_of_lt_of_le hp1 (by exact_mod_cast h1)
  rw [abs_inv_diff hr hm₁ hm₂]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have hc1 : (m₁ : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast h1
  have hc2 : (m₂ : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast h2
  nlinarith [hc1, hc2, hp1, hp2]

/-- The gap scale from above, when the pair is confined to `[M₀, M₁]`. -/
theorem abs_inv_diff_le {r : ℝ} (hr : 0 ≤ r) {m₁ m₂ M₀ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (hM₀ : 1 ≤ M₀) (h1 : M₀ ≤ m₁) (h2 : M₀ ≤ m₂) :
    |r / m₁ - r / m₂| ≤ r * |(m₂ : ℝ) - (m₁ : ℝ)| / ((M₀ : ℝ) * (M₀ : ℝ)) := by
  have hp1 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have hp2 : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂
  have hM : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀
  rw [abs_inv_diff hr hm₁ hm₂]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have hc1 : (M₀ : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast h1
  have hc2 : (M₀ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h2
  nlinarith [hc1, hc2, hM]

end

end RHTower.Sieve
