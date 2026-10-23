import GaloisForLFunctions.RHTower.Sieve.ZetaLandauGeneral
import GaloisForLFunctions.RHTower.Sieve.DeLaValleePoussinInequality

/-!
# The de la Vallée Poussin inequality at a general radius

The classical inequality uses Landau's lemma on a disc of radius `1/4` with the crude growth bound
`‖ζ‖ ≤ 7 + 2|γ|`, so its remainder is `≍ log|γ|` and the region it produces has width `≍ 1/log|γ|`.

Written against the pair `(R, Φ)` — a radius and a growth bound valid on the discs of radius `R₀ > R`
at heights `γ` and `2γ` — the remainder becomes `80 X / R` with

```text
X = (5/4) log Φ + (3/4) log(1 + 1/δ) + 6 ,
```

the `(3/4) log(1 + 1/δ)` coming from the three-four-one lower bound for `‖ζ(1+δ+iγ)‖`.  A growth
bound that is polylogarithmic on a strip of width `≍ R` therefore gives a remainder `≍ log Φ / R`,
which is the quantity a Littlewood-quality region has to make small.
-/

namespace RHTower.Sieve

open Complex Metric

/-- The reciprocal estimate against a general growth bound. -/
theorem neg_log_norm_riemannZeta_le_of {σ t Φ : ℝ} (hσ1 : 1 < σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ Φ) :
    -Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 3 / 4 * Real.log (1 + 1 / (σ - 1)) + 1 / 4 * Real.log Φ + 22 / 4 := by
  have hlow := exp_le_norm_riemannZeta_shift (σ := σ) (t := t) (B₀ := Φ) hσ1 hB
  have hz1 : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hz1pos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hz1
  have h := Real.log_le_log (Real.exp_pos _) hlow
  rw [Real.log_exp] at h
  linarith

/-- **The de la Vallée Poussin inequality against a radius and a growth bound.** -/
theorem dlvp_inequality_of_bound {β γ δ A R R₀ Φ : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hγ : 3 ≤ γ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    (hR0 : 0 < R) (hRR₀ : R < R₀) (hR₀1 : R₀ ≤ 1)
    (hΦ1 : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) R₀, ‖riemannZeta w‖ < Φ)
    (hΦ2 : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) R₀,
      ‖riemannZeta w‖ < Φ)
    (hΦ4 : ‖riemannZeta (((1 + δ : ℝ) : ℂ) + ((4 * γ : ℝ) : ℂ) * Complex.I)‖ ≤ Φ)
    (hΦ0 : 1 ≤ Φ)
    (hβ1 : β ≤ 1) (hclose : 1 + δ - β ≤ R / 2)
    (hzero : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0) :
    4 / (1 + δ - β)
      ≤ 3 / δ + 3 * A
        + 80 / R * (5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6) := by
  set σ : ℝ := 1 + δ with hσdef
  clear_value σ
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hsb : 0 < σ - β := by rw [hσdef]; linarith
  have hγ0 : (0 : ℝ) < γ := by linarith
  set c₁ : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hc₁def
  set c₂ : ℂ := (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I with hc₂def
  have hc₁re : c₁.re = σ := by rw [hc₁def]; simp
  have hc₁im : c₁.im = γ := by rw [hc₁def]; simp
  have hc₂re : c₂.re = σ := by rw [hc₂def]; simp
  have hc₂im : c₂.im = 2 * γ := by rw [hc₂def]; simp
  clear_value c₁
  clear_value c₂
  -- the balls avoid the pole
  have hne₁ : ∀ w ∈ ball c₁ R₀, w ≠ 1 := by
    intro w hw hcon
    subst hcon
    have hd : ‖(1 : ℂ) - c₁‖ < R₀ := by simpa [dist_eq_norm] using hw
    have h1 : |((1 : ℂ) - c₁).im| ≤ ‖(1 : ℂ) - c₁‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hc₁im] at h1
    simp only [Complex.one_im, zero_sub, abs_neg] at h1
    rw [abs_of_pos hγ0] at h1
    linarith
  have hne₂ : ∀ w ∈ ball c₂ R₀, w ≠ 1 := by
    intro w hw hcon
    subst hcon
    have hd : ‖(1 : ℂ) - c₂‖ < R₀ := by simpa [dist_eq_norm] using hw
    have h1 : |((1 : ℂ) - c₂).im| ≤ ‖(1 : ℂ) - c₂‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hc₂im] at h1
    simp only [Complex.one_im, zero_sub, abs_neg] at h1
    rw [abs_of_pos (by linarith)] at h1
    linarith
  -- Landau at height `γ`, retaining the zero
  obtain ⟨Z₁, m₁, _, hz₁, hmem₁, hmult₁, hkey₁⟩ :=
    zeta_landau_of_bound (c := c₁) (R := R) (R₀ := R₀) (Φ := Φ) hR0 hRR₀ hne₁
      (fun w hw => (hΦ1 w hw).le) (by rw [hc₁re]; linarith)
      (hΦ1 c₁ (Metric.mem_ball_self (by linarith)))
  have hρmem : ((β : ℂ) + (γ : ℂ) * Complex.I) ∈ Z₁ := by
    refine hmem₁ _ ?_ hzero
    have hdiff : ((β : ℂ) + (γ : ℂ) * Complex.I) - c₁ = (((β - σ : ℝ)) : ℂ) := by
      rw [hc₁def]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hsum₁ : ∑ ρ ∈ ({(β : ℂ) + (γ : ℂ) * Complex.I} : Finset ℂ), (m₁ ρ : ℝ)
      * ((c₁ - ρ)⁻¹).re = (m₁ ((β : ℂ) + (γ : ℂ) * Complex.I) : ℝ) * (1 / (σ - β)) := by
    rw [Finset.sum_singleton]
    congr 1
    have hdiff : c₁ - ((β : ℂ) + (γ : ℂ) * Complex.I) = (((σ - β : ℝ)) : ℂ) := by
      rw [hc₁def]; push_cast; ring
    rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have hone : (1 : ℝ) ≤ (m₁ ((β : ℂ) + (γ : ℂ) * Complex.I) : ℝ) := by
    exact_mod_cast hmult₁ _ hρmem
  have hkeyone := hkey₁ {(β : ℂ) + (γ : ℂ) * Complex.I}
    (Finset.singleton_subset_iff.mpr hρmem)
  rw [hsum₁] at hkeyone
  -- Landau at height `2γ`, retaining nothing
  obtain ⟨Z₂, m₂, _, hz₂, hmem₂, hmult₂, hkey₂⟩ :=
    zeta_landau_of_bound (c := c₂) (R := R) (R₀ := R₀) (Φ := Φ) hR0 hRR₀ hne₂
      (fun w hw => (hΦ2 w hw).le) (by rw [hc₂re]; linarith)
      (hΦ2 c₂ (Metric.mem_ball_self (by linarith)))
  have hkeytwo := hkey₂ ∅ (Finset.empty_subset _)
  rw [Finset.sum_empty, sub_zero] at hkeytwo
  -- the three-four-one inequality and the pole bound
  have h341 := zero_le_three_four_one_logDeriv (σ := σ) (t := γ) hσ1
  rw [neg_div_re_eq_neg_logDeriv_re, neg_div_re_eq_neg_logDeriv_re,
    neg_div_re_eq_neg_logDeriv_re] at h341
  have hcast2 : ((2 * γ : ℝ) : ℂ) = (2 * γ : ℂ) := by push_cast; ring
  rw [← hcast2, ← hc₁def, ← hc₂def] at h341
  have hpole := hA σ hσ1 hσ2
  rw [neg_div_re_eq_neg_logDeriv_re] at hpole
  have hpole' : -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / δ + A := by
    have hd : σ - 1 = δ := by rw [hσdef]; ring
    rw [hd] at hpole
    exact hpole
  -- the two Landau constants
  have hz1pos : (0 : ℝ) < ‖riemannZeta c₁‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by rw [hc₁re]; linarith))
  have hz2pos : (0 : ℝ) < ‖riemannZeta c₂‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by rw [hc₂re]; linarith))
  set X : ℝ := 5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6 with hXdef
  clear_value X
  have hδeq : Real.log (1 + 1 / (σ - 1)) = Real.log (1 + 1 / δ) := by
    have hd : σ - 1 = δ := by rw [hσdef]; ring
    rw [hd]
  have hB1 : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ Φ := by
    have := (hΦ2 c₂ (Metric.mem_ball_self (by linarith))).le
    rw [hc₂def, hcast2] at this
    exact this
  have hB2 : ‖riemannZeta ((σ : ℂ) + (2 * ((2 * γ : ℝ) : ℂ)) * Complex.I)‖ ≤ Φ := by
    have hrw : ((2 : ℂ) * (((2 * γ : ℝ)) : ℂ)) = ((4 * γ : ℝ) : ℂ) := by push_cast; ring
    rw [hrw]
    exact hΦ4
  have hM₁ : Real.log (Φ / ‖riemannZeta c₁‖) ≤ X := by
    rw [Real.log_div (by linarith) (ne_of_gt hz1pos)]
    have hden := neg_log_norm_riemannZeta_le_of (σ := σ) (t := γ) (Φ := Φ) hσ1 hB1
    rw [hδeq] at hden
    rw [hc₁def, hXdef]
    linarith
  have hM₂ : Real.log (Φ / ‖riemannZeta c₂‖) ≤ X := by
    rw [Real.log_div (by linarith) (ne_of_gt hz2pos)]
    have hden := neg_log_norm_riemannZeta_le_of (σ := σ) (t := 2 * γ) (Φ := Φ) hσ1 hB2
    rw [hδeq] at hden
    rw [hc₂def, hXdef]
    linarith
  -- assembling
  have hXpos : (0 : ℝ) < X := by
    have h1 : (0 : ℝ) ≤ Real.log Φ := Real.log_nonneg hΦ0
    have hinv : (0 : ℝ) < 1 / δ := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (1 + 1 / δ) := Real.log_nonneg (by linarith)
    rw [hXdef]; linarith
  have hone' : (1 : ℝ) / (σ - β) ≤ (m₁ ((β : ℂ) + (γ : ℂ) * Complex.I) : ℝ) * (1 / (σ - β)) := by
    have hpos : (0 : ℝ) < 1 / (σ - β) := by positivity
    nlinarith [hone, hpos]
  have hRinv : (0 : ℝ) < 16 / R := by positivity
  have hkey1' : -(logDeriv riemannZeta c₁).re ≤ 16 * X / R - 1 / (σ - β) := by
    have hmono : 16 * Real.log (Φ / ‖riemannZeta c₁‖) / R ≤ 16 * X / R :=
      div_le_div_of_nonneg_right (by linarith [hM₁]) hR0.le
    linarith [hkeyone, hone', hmono]
  have hkey2' : -(logDeriv riemannZeta c₂).re ≤ 16 * X / R := by
    have hmono : 16 * Real.log (Φ / ‖riemannZeta c₂‖) / R ≤ 16 * X / R :=
      div_le_div_of_nonneg_right (by linarith [hM₂]) hR0.le
    linarith [hkeytwo, hmono]
  have hdiv : 4 / (σ - β) = 4 * (1 / (σ - β)) := by ring
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hgoal : 4 / (σ - β) ≤ 3 / δ + 3 * A + 80 / R * X := by
    have e1 : 3 * -(logDeriv riemannZeta ((σ : ℂ))).re ≤ 3 * (1 / δ + A) :=
      mul_le_mul_of_nonneg_left hpole' (by norm_num)
    have e2 : 4 * -(logDeriv riemannZeta c₁).re ≤ 4 * (16 * X / R - 1 / (σ - β)) :=
      mul_le_mul_of_nonneg_left hkey1' (by norm_num)
    have hrw : (80 : ℝ) / R * X = 5 * (16 * X / R) := by field_simp; ring
    have hd3 : (3 : ℝ) / δ = 3 * (1 / δ) := by ring
    rw [hdiv, hrw, hd3]
    set Y : ℝ := 16 * X / R with hYdef
    clear_value Y
    set d : ℝ := 1 / δ with hddef
    clear_value d
    set sb : ℝ := 1 / (σ - β) with hsbdef
    clear_value sb
    linarith only [h341, e1, e2, hkey2']
  exact hgoal

end RHTower.Sieve
