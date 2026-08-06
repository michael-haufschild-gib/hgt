import GaloisForLFunctions.RHTower.Sieve.ZetaInvStripBound

/-!
# The strip bound in multiplicative form

`exists_neg_log_zeta_upper_strip` is stated logarithmically.  Exponentiating, and weakening the
exponent `7/4` to the integer `2` so that no real power is needed,

```text
‖ζ(σ + iγ)‖ ≥ c / log²|γ|      whenever  |σ - 1| ≤ log^{-2}|γ|.
```

This is the form a contour argument uses.  The nonvanishing that makes the logarithm invertible
comes from the zero-free region: the strip has width `log^{-2}|γ|`, well inside the region's
`c₀/log|γ|` once `log|γ| > 1/c₀`.
-/

namespace RHTower.Sieve

open Complex

/-- The strip sits inside the zero-free region. -/
theorem zeta_ne_zero_on_thin_strip {c₀ T₂ σ γ : ℝ} (hc₀0 : 0 < c₀)
    (hregion : ∀ β γ' : ℝ, T₂ ≤ |γ'| → β ≤ 1 → 1 - c₀ / Real.log |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
    (hγT₂ : T₂ ≤ |γ|) (hγ4 : 4 ≤ |γ|) (hLc : 1 / c₀ < Real.log |γ|)
    (hlow : 1 - 1 / Real.log |γ| ^ 2 ≤ σ) :
    riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  have hL1 := one_le_log_abs hγ4
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  rcases le_or_gt σ 1 with hle | hgt
  · refine hregion σ γ hγT₂ hle ?_
    have hcmp : 1 / Real.log |γ| ^ 2 < c₀ / Real.log |γ| := by
      rw [div_lt_div_iff₀ (by positivity) hL0]
      have h1 : (1 : ℝ) < c₀ * Real.log |γ| := by
        rw [div_lt_iff₀ hc₀0] at hLc
        nlinarith [hLc, hc₀0]
      nlinarith [h1, hL0]
    linarith
  · exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)

/-- **The strip bound, multiplicatively.** -/
theorem exists_zeta_lower_strip :
    ∃ c T : ℝ, 0 < c ∧ 4 ≤ T ∧ ∀ σ γ : ℝ, T ≤ |γ| →
      1 - 1 / Real.log |γ| ^ 2 ≤ σ → σ ≤ 1 + 1 / Real.log |γ| ^ 2 →
      c / Real.log |γ| ^ 2 ≤ ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ := by
  obtain ⟨C, T, hT, hbound⟩ := exists_neg_log_zeta_upper_strip
  obtain ⟨c₀, T₂, hc₀0, hT₂, hregion⟩ := exists_zero_free_region
  refine ⟨Real.exp (-C), max (max T 4) (max T₂ (Real.exp (1 / c₀ + 1))), by positivity, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro σ γ hγ hlow hhigh
  have hγT : T ≤ |γ| := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hγ)
  have hγ4 : (4 : ℝ) ≤ |γ| := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hγ)
  have hγT₂ : T₂ ≤ |γ| := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hγ)
  have hγexp : Real.exp (1 / c₀ + 1) ≤ |γ| :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hγ)
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hL1 := one_le_log_abs hγ4
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  have hLc : 1 / c₀ < Real.log |γ| := by
    have h := Real.le_log_iff_exp_le hγ0 |>.mpr hγexp
    linarith
  have hlogL : (0 : ℝ) ≤ Real.log (Real.log |γ|) := Real.log_nonneg hL1
  have hz := zeta_ne_zero_on_thin_strip hc₀0 hregion hγT₂ hγ4 hLc hlow
  have hzpos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hz
  have hb := hbound σ γ hγT hlow hhigh
  -- compare logarithms
  have hlhs : Real.log (Real.exp (-C) / Real.log |γ| ^ 2)
      = -C - 2 * Real.log (Real.log |γ|) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  have hcmp : Real.log (Real.exp (-C) / Real.log |γ| ^ 2)
      ≤ Real.log ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ := by
    rw [hlhs]
    linarith [hb, hlogL]
  exact (Real.log_le_log_iff (by positivity) hzpos).mp hcmp

end RHTower.Sieve
