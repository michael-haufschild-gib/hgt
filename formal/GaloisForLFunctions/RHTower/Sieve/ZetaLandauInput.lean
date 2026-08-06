import GaloisForLFunctions.RHTower.Sieve.LandauRealPart
import GaloisForLFunctions.RHTower.Sieve.ZetaCrudeGrowth
import GaloisForLFunctions.RHTower.Sieve.ZetaDerivBound

/-!
# Landau's lemma applied to `ζ`

At a centre `σ + iγ` with `1 < σ ≤ 2` and `|γ| ≥ 3`, the disc of radius `3/8` stays inside
`Re w ≥ 5/8` and `|Im w| ≥ 2`, so the crude growth bound applies there and

```text
‖ζ(w)‖ ≤ 7 + 2|γ|      on the disc.
```

Landau's lemma with `R = 1/4` therefore gives, for every subfamily `S` of the zeros within `1/8` of
the centre,

```text
-Re ζ'/ζ (σ + iγ) ≤ 64 log ((7 + 2|γ|)/‖ζ(σ+iγ)‖) - ∑_{ρ ∈ S} m_ρ Re (σ + iγ - ρ)⁻¹.
```

The retained family contains *every* zero within `1/8` of the centre, so a prescribed zero may be
kept.
-/

namespace RHTower.Sieve

open Metric Complex

/-- **Landau's lemma for `ζ` at a point of the strip.** -/
theorem zeta_landau_at {σ γ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hγ : 3 ≤ |γ|) :
    ∃ (Z₁ : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z₁, ‖ρ - ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 1 / 8) ∧
      (∀ ρ ∈ Z₁, riemannZeta ρ = 0) ∧
      (∀ w : ℂ, ‖w - ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 1 / 8 →
        riemannZeta w = 0 → w ∈ Z₁) ∧
      (∀ ρ ∈ Z₁, 1 ≤ m ρ) ∧
      ∀ S ⊆ Z₁,
        -(logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
          ≤ 64 * Real.log ((7 + 2 * |γ|)
              / ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖)
            - ∑ ρ ∈ S, (m ρ : ℝ)
                * ((((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re := by
  set c : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hcdef
  have hcre : c.re = σ := by rw [hcdef]; simp
  have hcim : c.im = γ := by rw [hcdef]; simp
  have hγ0 : (0 : ℝ) ≤ |γ| := abs_nonneg γ
  -- geometry of the disc
  have hdiscre : ∀ w ∈ ball c (3 / 8 : ℝ), 1 / 2 ≤ w.re := by
    intro w hw
    have hd : ‖w - c‖ < 3 / 8 := by simpa [dist_eq_norm] using hw
    have h1 : |(w - c).re| ≤ ‖w - c‖ := Complex.abs_re_le_norm _
    have h2 : (w - c).re = w.re - σ := by rw [Complex.sub_re, hcre]
    rw [h2] at h1
    have := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hd))
    linarith [this.1]
  have hdiscim : ∀ w ∈ ball c (3 / 8 : ℝ), 2 ≤ |w.im| := by
    intro w hw
    have hd : ‖w - c‖ < 3 / 8 := by simpa [dist_eq_norm] using hw
    have h1 : |(w - c).im| ≤ ‖w - c‖ := Complex.abs_im_le_norm _
    have h2 : (w - c).im = w.im - γ := by rw [Complex.sub_im, hcim]
    rw [h2] at h1
    have h3 : |w.im - γ| < 3 / 8 := lt_of_le_of_lt h1 hd
    have h4 := abs_le.mp h3.le
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases w.im with ⟨hw', _⟩ | ⟨hw', _⟩ <;> rw [hw'] <;> linarith [h4.1, h4.2, hγ]
  have hne1 : ∀ w ∈ ball c (3 / 8 : ℝ), w ≠ 1 := by
    intro w hw hcon
    have h := hdiscim w hw
    rw [hcon] at h
    simp at h
    linarith
  have hnormc : ‖c‖ ≤ 2 + |γ| := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im c) ?_
    rw [hcre, hcim]
    have : |σ| = σ := abs_of_pos (by linarith)
    rw [this]
    linarith
  -- analyticity and nonvanishing
  have hf : AnalyticOnNhd ℂ riemannZeta (ball c (3 / 8 : ℝ)) :=
    (differentiableOn_riemannZeta_of_ne_one hne1).analyticOnNhd isOpen_ball
  have hcball : c ∈ ball c (3 / 8 : ℝ) := by simp
  have hfc : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; linarith)
  have hfcpos : (0 : ℝ) < ‖riemannZeta c‖ := norm_pos_iff.mpr hfc
  -- the growth bound on the disc
  have hupper : ∀ w ∈ ball c (3 / 8 : ℝ), ‖riemannZeta w‖ ≤ 7 + 2 * |γ| := by
    intro w hw
    have hd : ‖w - c‖ < 3 / 8 := by simpa [dist_eq_norm] using hw
    have hwn : ‖w‖ ≤ ‖c‖ + 3 / 8 := by
      have := norm_add_le (w - c) c
      simp only [sub_add_cancel] at this
      linarith
    have := norm_riemannZeta_le_crude (hdiscre w hw) (hdiscim w hw)
    linarith
  set M : ℝ := (7 + 2 * |γ|) / ‖riemannZeta c‖ with hMdef
  have hM1 : 1 < M := by
    rw [hMdef, lt_div_iff₀ hfcpos, one_mul]
    have hcbound := norm_riemannZeta_le_crude (w := c)
      (by rw [hcre]; linarith) (by rw [hcim]; linarith)
    linarith
  have hbound : ∀ w ∈ ball c (3 / 8 : ℝ), ‖riemannZeta w‖ ≤ M * ‖riemannZeta c‖ := by
    intro w hw
    rw [hMdef, div_mul_cancel₀ _ (ne_of_gt hfcpos)]
    exact hupper w hw
  obtain ⟨Z₁, m, hZ₁, hzero, hmem, hmult, hkey⟩ :=
    neg_re_logDeriv_le (c := c) (R := 1 / 4) (R₀ := 3 / 8) (M := M)
      (by norm_num) (by norm_num) hM1 hf hfc hbound
  refine ⟨Z₁, m, fun ρ hρ => by linarith [hZ₁ ρ hρ], hzero, ?_, hmult, ?_⟩
  · intro w hw hfw
    exact hmem w (by linarith [hw]) hfw
  · intro S hS
    have hre : ∀ ρ ∈ Z₁, ρ.re ≤ c.re := by
      intro ρ hρ
      rw [hcre]
      by_contra hcon
      have hgt : σ < ρ.re := not_le.mp hcon
      exact riemannZeta_ne_zero_of_one_le_re (by linarith) (hzero ρ hρ)
    have h := hkey c (by rw [sub_self, norm_zero]; norm_num) hfc hre S hS
    have hconst : 16 * Real.log M / (1 / 4) = 64 * Real.log M := by ring
    rw [hconst] at h
    exact h

end RHTower.Sieve
