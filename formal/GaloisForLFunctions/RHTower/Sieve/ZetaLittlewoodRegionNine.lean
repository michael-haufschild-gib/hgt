import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegionAbs
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegion

/-!
# Littlewood's region from height nine

`exists_littlewood_zero_free_region_abs` has the right shape but only past an existential threshold,
which the parameter accounting forces to be astronomical.  On any *bounded* range of heights the
corpus's explicit exponent-nine region, valid from `|t| ≥ 9`, already contains a small enough
multiple of the Littlewood strip: `c·log log|t|/log|t| ≤ c₉/log⁹|t|` as soon as
`c ≤ c₉/(log⁸ T_b · log log T_b)`.

Shrinking the constant therefore extends the Littlewood shape all the way down to height `9`:

```text
∃ c > 0, ∀ β t, 9 ≤ |t| → β ≤ 1 → 1 - c·log log|t|/log|t| < β → ζ(β + it) ≠ 0 .
```
-/

namespace RHTower.Sieve

open Complex

/-- Below the asymptotic threshold the exponent-nine width dominates the Littlewood width. -/
theorem littlewood_of_kappa_nine {t Tb c : ℝ} (h9 : 9 ≤ |t|) (htTb : |t| ≤ Tb)
    (hc0 : 0 ≤ c) (hc : c ≤ zetaZeroFreeC / (Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb))) :
    c * Real.log (Real.log |t|) / Real.log |t| ≤ zetaZeroFreeC / Real.log |t| ^ (9 : ℕ) := by
  have h9pos : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have hlt : Real.log 9 ≤ Real.log |t| := Real.log_le_log (by norm_num) h9
  have hL1 : (1 : ℝ) < Real.log |t| := by
    have h2 : (2 : ℝ) < Real.log 9 := by
      have h8 : Real.log ((8 : ℝ)) ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
      have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      rw [h8eq] at h8
      linarith
    linarith
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hmono : Real.log |t| ≤ Real.log Tb := Real.log_le_log (by linarith) htTb
  have hTb1 : (1 : ℝ) < Real.log Tb := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log |t|) := Real.log_pos hL1
  have hLLmono : Real.log (Real.log |t|) ≤ Real.log (Real.log Tb) :=
    Real.log_le_log hL0 hmono
  have hLLTb0 : (0 : ℝ) < Real.log (Real.log Tb) := Real.log_pos hTb1
  have hpow : Real.log |t| ^ (8 : ℕ) ≤ Real.log Tb ^ (8 : ℕ) := pow_le_pow_left₀ hL0.le hmono 8
  have hpow0 : (0 : ℝ) < Real.log |t| ^ (8 : ℕ) := by positivity
  -- the target, cleared of denominators
  have hden : (0 : ℝ) < Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb) := by positivity
  have hc' : c * (Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb)) ≤ zetaZeroFreeC := by
    rw [le_div_iff₀ hden] at hc
    exact hc
  have hkey : c * (Real.log |t| ^ (8 : ℕ) * Real.log (Real.log |t|)) ≤ zetaZeroFreeC := by
    refine le_trans ?_ hc'
    have h1 : Real.log |t| ^ (8 : ℕ) * Real.log (Real.log |t|)
        ≤ Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb) := by
      nlinarith [hpow, hLLmono, hLL0, hpow0]
    nlinarith [h1, hc0]
  rw [div_le_div_iff₀ hL0 (by positivity)]
  have hsplit : Real.log |t| ^ (9 : ℕ) = Real.log |t| ^ (8 : ℕ) * Real.log |t| := by ring
  rw [hsplit]
  nlinarith [hkey, hL0, hpow0]

/-- **Littlewood's zero-free region from height nine.** -/
theorem exists_littlewood_zero_free_region_from_nine :
    ∃ c : ℝ, 0 < c ∧ ∀ β t : ℝ, 9 ≤ |t| → β ≤ 1 →
      1 - c * Real.log (Real.log |t|) / Real.log |t| < β →
      riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c₁, T, hc₁0, hT3, hregion⟩ := exists_littlewood_zero_free_region_abs
  set Tb : ℝ := max T 9 with hTbdef
  have hTb9 : (9 : ℝ) ≤ Tb := le_max_right _ _
  have hTbT : T ≤ Tb := le_max_left _ _
  have hTblog : (1 : ℝ) < Real.log Tb := by
    have h8 : Real.log ((8 : ℝ)) ≤ Real.log Tb := Real.log_le_log (by norm_num) (by linarith)
    have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    rw [h8eq] at h8
    linarith
  have hLLTb : (0 : ℝ) < Real.log (Real.log Tb) := Real.log_pos hTblog
  have hden : (0 : ℝ) < Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb) := by positivity
  refine ⟨min c₁ (zetaZeroFreeC / (Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb))),
    lt_min hc₁0 (div_pos zetaZeroFreeC_pos hden), ?_⟩
  intro β t h9 hβ1 hβ
  have hlt : Real.log 9 ≤ Real.log |t| := Real.log_le_log (by norm_num) h9
  have hL1 : (1 : ℝ) < Real.log |t| := by
    have h2 : (2 : ℝ) < Real.log 9 := by
      have h8 : Real.log ((8 : ℝ)) ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
      have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      rw [h8eq] at h8
      linarith
    linarith
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log |t|) := Real.log_pos hL1
  rcases le_or_gt Tb |t| with hbig | hsmall
  · refine hregion β t (le_trans hTbT hbig) hβ1 ?_
    have hstep : min c₁ (zetaZeroFreeC / (Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb)))
        * Real.log (Real.log |t|) / Real.log |t|
        ≤ c₁ * Real.log (Real.log |t|) / Real.log |t| := by
      refine div_le_div_of_nonneg_right ?_ hL0.le
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) hLL0.le
    linarith
  · refine riemannZeta_ne_zero_of_re_gt_one_sub h9 ?_
    have hstep := littlewood_of_kappa_nine
      (c := min c₁ (zetaZeroFreeC / (Real.log Tb ^ (8 : ℕ) * Real.log (Real.log Tb))))
      h9 (le_of_lt hsmall)
      (le_of_lt (lt_min hc₁0 (div_pos zetaZeroFreeC_pos hden))) (min_le_right _ _)
    linarith

end RHTower.Sieve
