import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRegionKappaOne
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegionBound

/-!
# The thin disc about `1 + iγ`

The segment used to transport `log‖ζ‖` across the abscissa has length `≍ log^{-2}|γ|`, so the disc
carrying it has radius `3 log^{-2}|γ|` about `σ₁ + iγ` with `σ₁ = 1 + log^{-2}|γ|`.  Every point of
that disc has real part above `1 - 2 log^{-2}|γ|` and height within `3` of `γ`, which puts it inside
the zero-free region once `log|γ| > 4/c`: the region's own width `c/log` beats `2 log^{-2}`.

The geometry is separated from the analytic assembly so that each proof carries a short context —
a single monolithic proof exceeds the elaboration budget.
-/

namespace RHTower.Sieve

open Complex Metric

/-- The real part of the thin disc's centre. -/
theorem thin_centre_re (γ L : ℝ) :
    ((((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re = 1 + 1 / L ^ (2 : ℕ) := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of the thin disc's centre. -/
theorem thin_centre_im (γ L : ℝ) :
    ((((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im]
  ring

/-- Real parts on the thin disc. -/
theorem thin_disc_re {γ L : ℝ} {w : ℂ}
    (hw : w ∈ ball (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ (2 : ℕ))) :
    1 - 2 / L ^ (2 : ℕ) < w.re := by
  have hd : ‖w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ < 3 / L ^ (2 : ℕ) := by
    simpa [dist_eq_norm] using hw
  have h1 : |(w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re|
      ≤ ‖w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _
  have h2 : (w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re
      = w.re - (1 + 1 / L ^ (2 : ℕ)) := by
    rw [Complex.sub_re, thin_centre_re]
  rw [h2] at h1
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 hd)
  have h4 : (3 : ℝ) / L ^ (2 : ℕ) = 1 / L ^ (2 : ℕ) + 2 / L ^ (2 : ℕ) := by ring
  linarith [h3.1, h4]

/-- Heights on the thin disc. -/
theorem thin_disc_im {γ L : ℝ} (hL3 : 3 ≤ L) {w : ℂ}
    (hw : w ∈ ball (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ (2 : ℕ))) :
    |w.im - γ| < 3 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hd : ‖w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ < 3 / L ^ (2 : ℕ) := by
    simpa [dist_eq_norm] using hw
  have h1 : |(w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im|
      ≤ ‖w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
  have h2 : (w - (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im = w.im - γ := by
    rw [Complex.sub_im, thin_centre_im]
  rw [h2] at h1
  have hRle : (3 : ℝ) / L ^ (2 : ℕ) ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hL3]
  linarith

/-- The height range on the thin disc. -/
theorem thin_disc_height {γ L T₂ : ℝ} (hL3 : 3 ≤ L) (hγ4 : 5 ≤ |γ|) (hγT₂ : T₂ + 3 ≤ |γ|)
    {w : ℂ} (hw : w ∈ ball (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ (2 : ℕ))) :
    T₂ ≤ |w.im| ∧ |w.im| ≤ 2 * |γ| := by
  have h := abs_le.mp (le_of_lt (thin_disc_im hL3 hw))
  constructor
  · rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases w.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [h.1, h.2, hγT₂]
  · rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases w.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [h.1, h.2, hγ4]

/-- The thin disc avoids the pole. -/
theorem thin_disc_ne_one {γ L : ℝ} (hL3 : 3 ≤ L) (hγ4 : 5 ≤ |γ|) {w : ℂ}
    (hw : w ∈ ball (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ (2 : ℕ))) :
    w ≠ 1 := by
  intro hcon
  have h := (thin_disc_height (T₂ := 1) hL3 hγ4 (by linarith) hw).1
  rw [hcon] at h
  norm_num [Complex.one_im] at h

/-- **Analyticity on the thin disc.** -/
theorem thin_disc_analytic {γ L : ℝ} (hL3 : 3 ≤ L) (hγ4 : 5 ≤ |γ|) :
    AnalyticOnNhd ℂ riemannZeta
      (ball (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ (2 : ℕ))) :=
  (differentiableOn_riemannZeta_of_ne_one fun _ hw => thin_disc_ne_one hL3 hγ4 hw).analyticOnNhd
    isOpen_ball

/-- **The thin disc is zero-free.** -/
theorem thin_disc_zerofree {c T₂ γ L : ℝ} (hc0 : 0 < c)
    (hregion : ∀ β γ' : ℝ, T₂ ≤ |γ'| → β ≤ 1 → 1 - c / Real.log |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
    (hL3 : 3 ≤ L) (hLc : 5 / c ≤ L) (hγ4 : 5 ≤ |γ|) (hγT₂ : T₂ + 3 ≤ |γ|)
    (hLdef : L = Real.log |γ|) {w : ℂ}
    (hw : w ∈ ball (((1 + 1 / L ^ (2 : ℕ) : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ (2 : ℕ))) :
    riemannZeta w ≠ 0 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  rcases le_or_gt 1 w.re with hge | hlt
  · exact riemannZeta_ne_zero_of_one_le_re hge
  obtain ⟨hlow, hup⟩ := thin_disc_height hL3 hγ4 hγT₂ hw
  have hone : (1 : ℝ) ≤ |w.im| := (thin_disc_height (T₂ := 1) hL3 hγ4 (by linarith) hw).1
  have himpos : (0 : ℝ) < |w.im| := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogim : Real.log |w.im| ≤ 2 * L := by
    have h1 : Real.log |w.im| ≤ Real.log (2 * |γ|) := Real.log_le_log himpos hup
    rw [Real.log_mul (by norm_num) (ne_of_gt hγ0)] at h1
    rw [hLdef]
    linarith
  have hlogimpos : (0 : ℝ) < Real.log |w.im| := by
    have h1 : (1 : ℝ) < |w.im| := by
      have h2 := (thin_disc_height (T₂ := 2) hL3 hγ4 (by linarith) hw).1
      linarith
    exact Real.log_pos h1
  have hstep : c / (2 * L) ≤ c / Real.log |w.im| :=
    div_le_div_of_nonneg_left hc0.le hlogimpos hlogim
  have htwo : 2 / L ^ (2 : ℕ) < c / (2 * L) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hLc, hc0, hL0, hL3, (div_le_iff₀ hc0).mp hLc]
  have hre := thin_disc_re hw
  have hgt : 1 - c / Real.log |w.im| < w.re := by linarith
  have h := hregion w.re w.im hlow (le_of_lt hlt) hgt
  rw [Complex.re_add_im] at h
  exact h

end RHTower.Sieve
