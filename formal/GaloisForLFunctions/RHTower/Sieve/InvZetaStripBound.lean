import GaloisForLFunctions.RHTower.Sieve.ZetaLowerStripMultiplicative
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular

/-!
# `1/ζ` on the width-`log^{-2}` strip, in regularised form

`exists_zeta_lower_strip` bounds `ζ` from below on `|σ - 1| ≤ log^{-2}|t|`.  Inverting it and
passing to the pole-free regularisation `invZeta s = (s-1)/((s-1)ζ(s))` gives

```text
‖invZeta(x + it)‖ ≤ C · log²|t|      whenever  |x - 1| ≤ log^{-2}|t|.
```

A contour whose abscissae are pinned to a parameter `K ≥ |t|` rather than to the height itself
gets the same bound with `log K` in place of `log |t|`: the strip widens and the bound weakens
monotonically in `K`, so both hypotheses transport in the right direction.
-/

namespace RHTower.Sieve

open Complex

/-- A point off the real axis is not the pole. -/
theorem strip_pt_ne_one {x t : ℝ} (ht : t ≠ 0) : ((x : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have him : ((x : ℂ) + (t : ℂ) * Complex.I).im = (1 : ℂ).im := by rw [h]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, Complex.one_im] at him
  exact ht (by linarith)

/-- **`1/ζ` on the thin strip.** -/
theorem exists_norm_invZeta_strip_le :
    ∃ C T : ℝ, 0 < C ∧ 4 ≤ T ∧ ∀ x t : ℝ, T ≤ |t| →
      1 - 1 / Real.log |t| ^ 2 ≤ x → x ≤ 1 + 1 / Real.log |t| ^ 2 →
      ‖invZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨c, T, hc0, hT4, hstrip⟩ := exists_zeta_lower_strip
  refine ⟨1 / c, T, by positivity, hT4, ?_⟩
  intro x t hT hx1 hx2
  have habs : (4 : ℝ) ≤ |t| := le_trans hT4 hT
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at habs
    simp only [abs_zero] at habs
    linarith
  have hL1 : (1 : ℝ) ≤ Real.log |t| := one_le_log_abs habs
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hb := hstrip x t hT hx1 hx2
  have hcL : (0 : ℝ) < c / Real.log |t| ^ 2 := by positivity
  have hzpos : (0 : ℝ) < ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ :=
    lt_of_lt_of_le hcL hb
  rw [norm_invZeta_eq (strip_pt_ne_one ht0), norm_inv, inv_eq_one_div, div_le_iff₀ hzpos]
  have hfac : (0 : ℝ) ≤ 1 / c * Real.log |t| ^ 2 := by positivity
  have hstep := mul_le_mul_of_nonneg_left hb hfac
  have heq : 1 / c * Real.log |t| ^ 2 * (c / Real.log |t| ^ 2) = 1 := by
    field_simp
  linarith [hstep, heq]

/-- **`1/ζ` on the strip pinned to a contour parameter.**  The abscissae are given in terms of
`log K` for a parameter `K` at least the height; monotonicity in `K` supplies both the wider
strip and the weaker bound. -/
theorem exists_norm_invZeta_contour_le :
    ∃ C T : ℝ, 0 < C ∧ 4 ≤ T ∧ ∀ x t K : ℝ, T ≤ |t| → |t| ≤ K →
      1 - 1 / Real.log K ^ 2 ≤ x → x ≤ 1 + 1 / Real.log K ^ 2 →
      ‖invZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log K ^ 2 := by
  obtain ⟨C, T, hC0, hT4, hbound⟩ := exists_norm_invZeta_strip_le
  refine ⟨C, T, hC0, hT4, ?_⟩
  intro x t K hT htK hx1 hx2
  have habs : (4 : ℝ) ≤ |t| := le_trans hT4 hT
  have hL1 : (1 : ℝ) ≤ Real.log |t| := one_le_log_abs habs
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hmono : Real.log |t| ≤ Real.log K := Real.log_le_log (by linarith) htK
  have hpow : Real.log |t| ^ 2 ≤ Real.log K ^ 2 := pow_le_pow_left₀ hL0.le hmono 2
  have hwidth : 1 / Real.log K ^ 2 ≤ 1 / Real.log |t| ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
  have hres := hbound x t hT (by linarith) (by linarith)
  have hfin : C * Real.log |t| ^ 2 ≤ C * Real.log K ^ 2 :=
    mul_le_mul_of_nonneg_left hpow hC0.le
  linarith

end RHTower.Sieve
