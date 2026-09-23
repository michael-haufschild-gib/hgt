import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRegionKappaOne
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegion

/-!
# The exponent-one region, valid from height nine

`exists_zero_free_region` has the right shape `1 - c/log|t|` but only past an astronomically large
threshold.  The corpus's explicit exponent-nine region
`RHTower.riemannZeta_ne_zero_of_re_gt_one_sub` is valid from `|t| ≥ 9`, and on any *bounded* range
of heights its width `c₉/log⁹|t|` dominates a small enough multiple of `1/log|t|`.

Shrinking the constant therefore extends the exponent-one shape all the way down to height `9`:

```text
∃ c > 0, ∀ β t, 9 ≤ |t| → β ≤ 1 → 1 - c/log|t| < β → ζ(β + it) ≠ 0.
```

The constant is very small — it is `c₉/log⁸T` with `T` the asymptotic threshold — but the shape and
the range of validity are what a consumer needs.
-/

namespace RHTower.Sieve

open Complex

/-- Below the asymptotic threshold, the exponent-nine width dominates. -/
theorem kappa_one_of_kappa_nine {t Tb c : ℝ} (h9 : 9 ≤ |t|) (hTb : 9 ≤ Tb) (htTb : |t| ≤ Tb)
    (hc : c ≤ zetaZeroFreeC / Real.log Tb ^ (8 : ℕ)) :
    c / Real.log |t| ≤ zetaZeroFreeC / Real.log |t| ^ (9 : ℕ) := by
  have h9pos : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have hlt : Real.log 9 ≤ Real.log |t| := Real.log_le_log (by norm_num) h9
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hTb0 : (0 : ℝ) < Real.log Tb := by
    have : Real.log 9 ≤ Real.log Tb := Real.log_le_log (by norm_num) hTb
    linarith
  have hmono : Real.log |t| ≤ Real.log Tb := Real.log_le_log (by linarith) htTb
  have hpow : Real.log |t| ^ (8 : ℕ) ≤ Real.log Tb ^ (8 : ℕ) := by
    exact pow_le_pow_left₀ hL0.le hmono 8
  have hstep : zetaZeroFreeC / Real.log Tb ^ (8 : ℕ) ≤ zetaZeroFreeC / Real.log |t| ^ (8 : ℕ) := by
    refine div_le_div_of_nonneg_left zetaZeroFreeC_pos.le (by positivity) hpow
  have hc' : c ≤ zetaZeroFreeC / Real.log |t| ^ (8 : ℕ) := le_trans hc hstep
  have hsplit : zetaZeroFreeC / Real.log |t| ^ (9 : ℕ)
      = (zetaZeroFreeC / Real.log |t| ^ (8 : ℕ)) / Real.log |t| := by
    rw [div_div, ← pow_succ]
  rw [hsplit]
  exact div_le_div_of_nonneg_right hc' hL0.le

/-- **The exponent-one zero-free region from height nine.** -/
theorem exists_zero_free_region_from_nine :
    ∃ c : ℝ, 0 < c ∧ ∀ β t : ℝ, 9 ≤ |t| → β ≤ 1 → 1 - c / Real.log |t| < β →
      riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c₁, T, hc₁0, hT3, hregion⟩ := exists_zero_free_region
  set Tb : ℝ := max T 9 with hTbdef
  have hTb9 : (9 : ℝ) ≤ Tb := le_max_right _ _
  have hTbT : T ≤ Tb := le_max_left _ _
  have hTb0 : (0 : ℝ) < Real.log Tb := by
    have h9pos : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
    have : Real.log 9 ≤ Real.log Tb := Real.log_le_log (by norm_num) hTb9
    linarith
  refine ⟨min c₁ (zetaZeroFreeC / Real.log Tb ^ (8 : ℕ)),
    lt_min hc₁0 (div_pos zetaZeroFreeC_pos (by positivity)), ?_⟩
  intro β t h9 hβ1 hβ
  have h9pos : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have hlt : Real.log 9 ≤ Real.log |t| := Real.log_le_log (by norm_num) h9
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  rcases le_or_gt Tb |t| with hbig | hsmall
  · -- past the asymptotic threshold
    refine hregion β t (le_trans hTbT hbig) hβ1 ?_
    have hstep : min c₁ (zetaZeroFreeC / Real.log Tb ^ (8 : ℕ)) / Real.log |t| ≤ c₁ / Real.log |t| :=
      div_le_div_of_nonneg_right (min_le_left _ _) hL0.le
    linarith
  · -- below it, the exponent-nine region already contains the strip
    refine riemannZeta_ne_zero_of_re_gt_one_sub h9 ?_
    have hstep := kappa_one_of_kappa_nine (c := min c₁ (zetaZeroFreeC / Real.log Tb ^ (8 : ℕ)))
      h9 hTb9 (le_of_lt hsmall) (min_le_right _ _)
    linarith

end RHTower.Sieve
