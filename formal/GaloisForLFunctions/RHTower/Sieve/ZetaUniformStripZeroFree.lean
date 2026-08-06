import GaloisForLFunctions.RHTower.Sieve.ZetaLowerStripMultiplicative
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRectangle

/-!
# Zero-freeness of the width-`log^{-2}` strip, uniformly in the height

Above the height at which the exponent-one zero-free region takes over, the strip
`1 - log^{-2}K ≤ Re s` is zero-free because `ζ` is bounded below there.  Below that height the
strip meets a compact box, on which a zero-free neighbourhood of the abscissa exists by
compactness.  Fitting the two costs only `log K ≥ 1/δ`:

```text
1 - log^{-2}K ≤ Re s,  |Im s| ≤ K,  s ≠ 1   ⟹   ζ(s) ≠ 0.
```

The strip is pinned to a contour parameter `K` rather than to the height of `s`, which is the form
a truncated rectangle needs: one width for the whole left edge.
-/

namespace RHTower.Sieve

open Complex

/-- **The strip is zero-free, uniformly up to height `K`.** -/
theorem exists_zeta_uniform_strip_zero_free :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (s : ℂ) (K : ℝ), L₀ ≤ Real.log K → |s.im| ≤ K →
      1 - 1 / Real.log K ^ 2 ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨c, T, hc0, hT4, hstrip⟩ := exists_zeta_lower_strip
  obtain ⟨δ, hδ0, hbox⟩ := exists_zero_free_box T
  refine ⟨max 1 (1 / δ), le_max_left _ _, ?_⟩
  intro s K hL hKim hre hne
  have hL1 : (1 : ℝ) ≤ Real.log K := le_trans (le_max_left _ _) hL
  have hLδ : 1 / δ ≤ Real.log K := le_trans (le_max_right _ _) hL
  have hLsq : (1 : ℝ) ≤ Real.log K ^ 2 := by nlinarith
  rcases le_or_gt 1 s.re with hx1 | hx1
  · exact riemannZeta_ne_zero_of_one_le_re hx1
  have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im s).symm
  rcases le_or_gt T |s.im| with hbig | hsmall
  · -- above the threshold: the lower bound on `ζ` forbids a zero
    have habs4 : (4 : ℝ) ≤ |s.im| := le_trans hT4 hbig
    have hLt1 : (1 : ℝ) ≤ Real.log |s.im| := one_le_log_abs habs4
    have hmono : Real.log |s.im| ≤ Real.log K := Real.log_le_log (by linarith) hKim
    have hpow : Real.log |s.im| ^ 2 ≤ Real.log K ^ 2 :=
      pow_le_pow_left₀ (by linarith) hmono 2
    have hwidth : 1 / Real.log K ^ 2 ≤ 1 / Real.log |s.im| ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    have hpos : (0 : ℝ) < 1 / Real.log |s.im| ^ 2 := by positivity
    have hb := hstrip s.re s.im hbig (by linarith) (by linarith)
    have hcL : (0 : ℝ) < c / Real.log |s.im| ^ 2 := by positivity
    have hzpos : (0 : ℝ) < ‖riemannZeta (((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I)‖ :=
      lt_of_lt_of_le hcL hb
    rw [hsplit]
    exact norm_pos_iff.mp hzpos
  · -- below it: the compact box carries a zero-free neighbourhood of the abscissa
    have hδcmp : 1 / Real.log K ^ 2 ≤ δ := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : (1 : ℝ) ≤ δ * Real.log K := by
        rw [div_le_iff₀ hδ0] at hLδ
        nlinarith [hLδ, hδ0]
      nlinarith [h1, hL1, hδ0]
    exact hbox s (by linarith) (le_of_lt hx1) (le_of_lt hsmall) hne

end RHTower.Sieve
