import GaloisForLFunctions.RHTower.DigammaTwoSided

/-!
# The zero-free region in unrestricted form

Every nontrivial zero has `|Im ρ| ≥ 4`, so the strip `|Im s| < 4` is zero-free outright and the
region can be stated for every `s` at once, with the scale `log (|Im s| + 4)` in place of
`log |Im s|`:

```text
0 < Re s  →  1 − 1/(58 log (|Im s| + 4)) < Re s  →  ζ(s) ≠ 0 .
```

No threshold, no case hypothesis on the ordinate, and `Re s ≥ 1` is covered by
`riemannZeta_ne_zero_of_one_le_re`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The strip `|Im s| < 4` is zero-free.** -/
theorem riemannZeta_ne_zero_of_abs_im_lt_four {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| < 4) : riemannZeta s ≠ 0 := by
  intro hzero
  have h4 := four_le_abs_im_of_zeta_zero h0 h1 hzero
  linarith

/-- **The unrestricted zero-free region.** -/
theorem riemannZeta_ne_zero_of_lt_re {s : ℂ} (h0 : 0 < s.re)
    (hs : 1 - 1 / 58 / Real.log (|s.im| + 4) < s.re) : riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  rcases lt_or_ge |s.im| 4 with him | him
  · exact riemannZeta_ne_zero_of_abs_im_lt_four h0 h1 him
  · intro hzero
    have hup := re_le_one_sub_of_zeta_zero h0 h1 hzero
    have hlogpos : (0 : ℝ) < Real.log |s.im| := Real.log_pos (by linarith)
    have hmono : Real.log |s.im| ≤ Real.log (|s.im| + 4) :=
      Real.log_le_log (by linarith) (by linarith)
    have hcmp : 1 / 58 / Real.log (|s.im| + 4) ≤ 1 / 58 / Real.log |s.im| := by
      apply div_le_div_of_nonneg_left (by norm_num) hlogpos hmono
    linarith

/-- The same, in the `(β, t)` coordinates used by the corpus's region interfaces. -/
theorem riemannZeta_ne_zero_of_lt_re_coords {β t : ℝ} (h0 : 0 < β)
    (hβ : 1 - 1 / 58 / Real.log (|t| + 4) < β) :
    riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hre : (((β : ℂ) + (t : ℂ) * Complex.I)).re = β := by simp
  have him : (((β : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  refine riemannZeta_ne_zero_of_lt_re (by rw [hre]; exact h0) ?_
  rw [hre, him]
  exact hβ

end

end RHTower
