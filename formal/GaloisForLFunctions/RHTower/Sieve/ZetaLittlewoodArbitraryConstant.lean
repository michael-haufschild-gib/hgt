import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivLittlewoodBound

/-!
# The exponent-one region with an arbitrary constant

The corpus's exponent-one region `exists_zero_free_region` produces *one* constant, and everything
downstream is limited by it: an argument that needs `1 - A/log|t|` zero-free for a prescribed `A`
cannot use it.

A region of Littlewood width does not have that limitation.  Since `A/log|t| ≤ c·log log|t|/log|t|`
as soon as `A ≤ c·log log|t|`, the Littlewood region contains the strip `1 - A/log|t|` for **every**
`A`, past a threshold depending on `A`:

```text
∀ A > 0, ∃ T, ∀ β t,  T ≤ |t|,  β ≤ 1,  1 - A/log|t| < β  ⟹  ζ(β + it) ≠ 0 .
```

The same substitution carries the logarithmic-derivative bound: `‖ζ'/ζ‖ ≤ C log²|γ|` holds on the
strip of width `A/log|γ|` for every `A`, where the exponent-one input gives it only for one `A`.
-/

namespace RHTower.Sieve

open Complex

/-- **The zero-free region with an arbitrary exponent-one constant.** -/
theorem exists_zero_free_region_arbitrary_constant (A : ℝ) :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ β t : ℝ, T ≤ |t| → β ≤ 1 → 1 - A / Real.log |t| < β →
      riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c, T₀, hc0, hT₀, hregion⟩ := exists_littlewood_zero_free_region_abs
  refine ⟨max T₀ (Real.exp (Real.exp (A / c))), le_trans hT₀ (le_max_left _ _), ?_⟩
  intro β t hγT hβ1 hβ
  have hT₀t : T₀ ≤ |t| := le_trans (le_max_left _ _) hγT
  have hexp : Real.exp (Real.exp (A / c)) ≤ |t| := le_trans (le_max_right _ _) hγT
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hlog : Real.exp (A / c) ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le ht0]
    exact hexp
  have hL0 : (0 : ℝ) < Real.log |t| := lt_of_lt_of_le (Real.exp_pos _) hlog
  have hAc : A / c ≤ Real.log (Real.log |t|) := by
    rw [Real.le_log_iff_exp_le hL0]
    exact hlog
  refine hregion β t hT₀t hβ1 ?_
  have hstep : A / Real.log |t| ≤ c * Real.log (Real.log |t|) / Real.log |t| := by
    refine div_le_div_of_nonneg_right ?_ hL0.le
    rw [div_le_iff₀ hc0] at hAc
    linarith
  linarith

/-- **The logarithmic-derivative bound on a strip of any prescribed exponent-one width.** -/
theorem exists_logDeriv_zeta_bound_arbitrary_constant (A : ℝ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ σ γ : ℝ, T ≤ |γ| → 1 - A / Real.log |γ| ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ 2 / Real.log (Real.log |γ|) := by
  obtain ⟨c, C, T₀, hc0, hC0, hT₀, hb⟩ := exists_logDeriv_zeta_bound_littlewood
  refine ⟨C, max T₀ (Real.exp (Real.exp (A / c))), hC0, ?_, ?_⟩
  · exact lt_of_lt_of_le hT₀ (le_max_left _ _)
  intro σ γ hγT hσlow hσ98
  have hT₀γ : T₀ ≤ |γ| := le_trans (le_max_left _ _) hγT
  have hexp : Real.exp (Real.exp (A / c)) ≤ |γ| := le_trans (le_max_right _ _) hγT
  have hγ0 : (0 : ℝ) < |γ| := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hlog : Real.exp (A / c) ≤ Real.log |γ| := by
    rw [Real.le_log_iff_exp_le hγ0]
    exact hexp
  have hL0 : (0 : ℝ) < Real.log |γ| := lt_of_lt_of_le (Real.exp_pos _) hlog
  have hAc : A / c ≤ Real.log (Real.log |γ|) := by
    rw [Real.le_log_iff_exp_le hL0]
    exact hlog
  refine hb σ γ hT₀γ ?_ hσ98
  have hstep : A / Real.log |γ| ≤ c * Real.log (Real.log |γ|) / Real.log |γ| := by
    refine div_le_div_of_nonneg_right ?_ hL0.le
    rw [div_le_iff₀ hc0] at hAc
    linarith
  linarith

end RHTower.Sieve
