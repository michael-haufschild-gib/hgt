import Mathlib

/-!
# Escape of the interaction degree

When the mean interaction degree diverges, the Chebyshev bound on the probability of staying below
any fixed degree tends to zero.  The analytic core is that `μ / (μ − D)²` vanishes as `μ → ∞` for
every fixed threshold `D`: past `μ ≥ 2D`, the gap `μ − D` is at least `μ/2`, so the bound is at
most `4/μ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **The Chebyshev escape bound vanishes.**  For a fixed degree threshold `D`, the ratio
`μ / (μ − D)²` tends to zero as the mean `μ` diverges. -/
theorem tendsto_mean_div_gap_sq (D : ℝ) :
    Tendsto (fun μ : ℝ => μ / (μ - D) ^ 2) atTop (𝓝 0) := by
  have hbig : ∀ᶠ μ : ℝ in atTop, max (2 * D) 0 + 1 ≤ μ := eventually_ge_atTop _
  have hnonneg : ∀ᶠ μ : ℝ in atTop, 0 ≤ μ / (μ - D) ^ 2 := by
    filter_upwards [hbig] with μ hμ
    have hμ0 : (0 : ℝ) ≤ μ := le_trans (by positivity) hμ
    positivity
  have hle : ∀ᶠ μ : ℝ in atTop, μ / (μ - D) ^ 2 ≤ 4 * μ⁻¹ := by
    filter_upwards [hbig] with μ hμ
    have h2D : 2 * D ≤ max (2 * D) 0 := le_max_left _ _
    have h0 : (0 : ℝ) ≤ max (2 * D) 0 := le_max_right _ _
    have hμpos : (0 : ℝ) < μ := by linarith
    have hgap : μ / 2 ≤ μ - D := by linarith
    have hgappos : (0 : ℝ) < μ / 2 := by linarith
    have hsq : μ ^ 2 / 4 ≤ (μ - D) ^ 2 := by nlinarith
    have hsqpos : (0 : ℝ) < μ ^ 2 / 4 := by positivity
    calc μ / (μ - D) ^ 2 ≤ μ / (μ ^ 2 / 4) := by
          exact div_le_div_of_nonneg_left hμpos.le hsqpos hsq
      _ = 4 * μ⁻¹ := by field_simp
  have hzero : Tendsto (fun μ : ℝ => 4 * μ⁻¹) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.const_mul (4 : ℝ)
    simpa using h
  exact squeeze_zero' hnonneg hle hzero

end GaloisForLFunctions.HTGeometry
