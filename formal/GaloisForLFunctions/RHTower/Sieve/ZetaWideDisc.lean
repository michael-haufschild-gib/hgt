import GaloisForLFunctions.RHTower.Sieve.ZetaLandauInput
import GaloisForLFunctions.RHTower.Sieve.DeLaValleePoussinInequality

/-!
# The wide disc around `9/8 + iγ`

Landau's lemma reaches only the eighth of its radius, so to get from the abscissa into the
zero-free region the disc must have radius above `1`.  The disc of radius `11/10` around
`9/8 + iγ` is the largest convenient one that still keeps `Re w > 0`, where the truncation at
`N = 1` gives a growth bound:

```text
Re w ≥ 1/40,   |Im w| ≥ 2,   ‖ζ(w)‖ ≤ 91 + 40|γ|      (|γ| ≥ 4).
```

Its eighth-radius `21/160` reaches `σ = 159/160 < 1`, so a point of the zero-free region is in
range.
-/

namespace RHTower.Sieve

open Metric Complex

/-- The crude growth bound with an arbitrary positive abscissa. -/
theorem norm_riemannZeta_le_crude_of_re_ge {w : ℂ} {η : ℝ} (hη : 0 < η) (hre : η ≤ w.re)
    (him : 2 ≤ |w.im|) : ‖riemannZeta w‖ ≤ 2 + ‖w‖ / η := by
  have hw0 : 0 < w.re := lt_of_lt_of_le hη hre
  have hsub : ‖w - 1‖ ≥ 2 := by
    have h1 : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
    have h2 : (w - 1).im = w.im := by simp
    rw [h2] at h1
    linarith
  have hwne1 : w ≠ 1 := by
    intro hcon
    rw [hcon] at hsub
    simp at hsub
    linarith
  have hmain := norm_riemannZeta_le_partialSum hw0 hwne1 (N := 1) le_rfl
  rw [sum_Icc_one_one_cpow] at hmain
  have hone1 : ((1 : ℕ) : ℝ) ^ (1 - w.re) = 1 := by norm_num
  have hone2 : ((1 : ℕ) : ℝ) ^ (-w.re) = 1 := by norm_num
  rw [hone1, hone2] at hmain
  have hsubpos : (0 : ℝ) < ‖w - 1‖ := by linarith
  have hinv : 1 / ‖w - 1‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hsubpos (by norm_num)]
    linarith
  have hquot : ‖w‖ * (1 / w.re) ≤ ‖w‖ / η := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hη hre
  simp only [norm_one] at hmain
  linarith

/-- The centre's real part. -/
theorem wide_centre_re (γ : ℝ) : ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re = 9 / 8 := by
  simp

/-- The centre's imaginary part. -/
theorem wide_centre_im (γ : ℝ) : ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by
  simp

/-- Real parts on the wide disc. -/
theorem wide_disc_re {γ : ℝ} {w : ℂ}
    (hw : w ∈ ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (11 / 10 : ℝ)) :
    (1 / 40 : ℝ) ≤ w.re := by
  have hd : ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ < 11 / 10 := by
    simpa [dist_eq_norm] using hw
  have h1 : |(w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re|
      ≤ ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _
  have h2 : (w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re = w.re - 9 / 8 := by
    rw [Complex.sub_re, wide_centre_re]
  rw [h2] at h1
  have h3 := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hd))
  linarith [h3.1]

/-- Imaginary parts on the wide disc. -/
theorem wide_disc_im {γ : ℝ} (hγ : 4 ≤ |γ|) {w : ℂ}
    (hw : w ∈ ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (11 / 10 : ℝ)) :
    (2 : ℝ) ≤ |w.im| := by
  have hd : ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ < 11 / 10 := by
    simpa [dist_eq_norm] using hw
  have h1 : |(w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im|
      ≤ ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
  have h2 : (w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im = w.im - γ := by
    rw [Complex.sub_im, wide_centre_im]
  rw [h2] at h1
  have h4 := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hd))
  rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
    rcases abs_cases w.im with ⟨hw', _⟩ | ⟨hw', _⟩ <;> rw [hw'] <;>
      linarith [h4.1, h4.2, hγ]

/-- Norms on the wide disc. -/
theorem wide_disc_norm {γ : ℝ} {w : ℂ}
    (hw : w ∈ ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (11 / 10 : ℝ)) :
    ‖w‖ ≤ 9 / 8 + |γ| + 11 / 10 := by
  have hd : ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ < 11 / 10 := by
    simpa [dist_eq_norm] using hw
  have hc : ‖(((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 9 / 8 + |γ| := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    rw [wide_centre_re, wide_centre_im]
    have : |(9 : ℝ) / 8| = 9 / 8 := abs_of_pos (by norm_num)
    rw [this]
  have hstep := norm_add_le (w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
    (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
  simp only [sub_add_cancel] at hstep
  linarith

/-- **The growth bound on the wide disc.** -/
theorem zeta_wide_disc_bound {γ : ℝ} (hγ : 4 ≤ |γ|) {w : ℂ}
    (hw : w ∈ ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (11 / 10 : ℝ)) :
    ‖riemannZeta w‖ ≤ 91 + 40 * |γ| := by
  have hcr := norm_riemannZeta_le_crude_of_re_ge (w := w) (η := 1 / 40) (by norm_num)
    (wide_disc_re hw) (wide_disc_im hγ hw)
  have hdiv : ‖w‖ / (1 / 40 : ℝ) = 40 * ‖w‖ := by ring
  rw [hdiv] at hcr
  have hn := wide_disc_norm hw
  linarith

/-- The wide disc avoids the pole. -/
theorem wide_disc_ne_one {γ : ℝ} (hγ : 4 ≤ |γ|) {w : ℂ}
    (hw : w ∈ ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (11 / 10 : ℝ)) : w ≠ 1 := by
  intro hcon
  have h := wide_disc_im hγ hw
  rw [hcon] at h
  simp at h
  linarith

/-- **Analyticity on the wide disc.** -/
theorem zeta_analytic_wide {γ : ℝ} (hγ : 4 ≤ |γ|) :
    AnalyticOnNhd ℂ riemannZeta
      (ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (11 / 10 : ℝ)) :=
  (differentiableOn_riemannZeta_of_ne_one fun _ hw => wide_disc_ne_one hγ hw).analyticOnNhd
    isOpen_ball

end RHTower.Sieve
