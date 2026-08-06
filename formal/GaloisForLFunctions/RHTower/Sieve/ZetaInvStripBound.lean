import GaloisForLFunctions.RHTower.Sieve.ZetaThinSegment
import GaloisForLFunctions.RHTower.Sieve.ZetaLowerNearAbscissa
import GaloisForLFunctions.RHTower.Sieve.LogNormSegment

/-!
# `1/ζ` on a strip of width `log^{-2}`

The lower bound `‖ζ(σ₁+iγ)‖ ≫ (log|γ|)^{-7/4}` at `σ₁ = 1 + log^{-2}|γ|` transports across the
abscissa along a segment of length at most `2 log^{-2}|γ|`, on which `‖ζ'/ζ‖ ≤ C log²|γ|`.  The
transport therefore costs the **constant** `2C`, and

```text
-log‖ζ(σ + iγ)‖ ≤ (7/4) log log|γ| + C'      whenever  |σ - 1| ≤ log^{-2}|γ|.
```

The vendored `PNTPlus.ZetaLowerBnd` gives `‖ζ‖ ≫ (log|t|)^{-7}` on width `log^{-9}|t|`; this is
`(log|γ|)^{-7/4}` on width `log^{-2}|γ|`.
-/

namespace RHTower.Sieve

open Complex Metric

/-- **`1/ζ` on a strip of width `log^{-2}` about the abscissa.** -/
theorem exists_neg_log_zeta_upper_strip :
    ∃ C T : ℝ, 4 ≤ T ∧ ∀ σ γ : ℝ, T ≤ |γ| →
      1 - 1 / Real.log |γ| ^ 2 ≤ σ → σ ≤ 1 + 1 / Real.log |γ| ^ 2 →
      -Real.log ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
        ≤ 7 / 4 * Real.log (Real.log |γ|) + C := by
  obtain ⟨C₀, T₀, hT₀, hσ₁bound⟩ := exists_neg_log_zeta_upper
  obtain ⟨c', C_D, T₁, hc'0, hCD0, hT₁, hLD⟩ := exists_logDeriv_zeta_bound
  obtain ⟨c, T₂, hc0, hT₂, hregion⟩ := exists_zero_free_region
  refine ⟨C₀ + 2 * C_D,
    max (max T₀ T₁) (max (T₂ + 3) (max 5 (Real.exp (max 3 (max (5 / c) (1 / c')))))),
    le_trans hT₀ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro σ γ hγT hσlow hσhigh
  have hγT₀ : T₀ ≤ |γ| := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hγT)
  have hγT₁ : T₁ ≤ |γ| := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hγT)
  have hγT₂ : T₂ + 3 ≤ |γ| := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hγT)
  have hγ5 : (5 : ℝ) ≤ |γ| :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hγT))
  have hγexp : Real.exp (max 3 (max (5 / c) (1 / c'))) ≤ |γ| :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hγT))
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  set L : ℝ := Real.log |γ| with hLdef
  have hLbig : max 3 (max (5 / c) (1 / c')) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hγ0]
    exact hγexp
  have hL3 : (3 : ℝ) ≤ L := le_trans (le_max_left _ _) hLbig
  have hLc : 5 / c ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLbig)
  have hLc' : 1 / c' ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLbig)
  have hL0 : (0 : ℝ) < L := by linarith
  have hR0 : (0 : ℝ) < 3 / L ^ 2 := by positivity
  -- the transport
  have htrans := abs_log_norm_sub_le (g := riemannZeta) hR0
    (thin_disc_analytic hL3 hγ5)
    (fun w hw => thin_disc_zerofree hc0 hregion hL3 hLc hγ5 hγT₂ hLdef hw)
    (thin_seg_endpoint hL0 hσlow hσhigh) (thin_centre_mem hL0)
    (fun t ht => thin_seg_mem hL0 hσlow hσhigh ht)
    (fun t ht => thin_seg_logDeriv hLD hγT₁ hLdef hL3 hc'0 hLc' hσlow hσhigh ht)
  -- the cost is a constant
  have hdist := thin_seg_dist (σ := σ) (γ := γ) (L := L) hσlow hσhigh
  have hcost : C_D * L ^ 2 * ‖((σ : ℂ) + (γ : ℂ) * Complex.I)
      - (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 2 * C_D := by
    have hfac : (0 : ℝ) ≤ C_D * L ^ 2 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hdist hfac
    have heq : C_D * L ^ 2 * (2 / L ^ 2) = 2 * C_D := by
      field_simp
    linarith [hstep, heq]
  -- the source bound
  have hsource := hσ₁bound γ hγT₀
  rw [← hLdef] at hsource
  have habs := abs_le.mp htrans
  linarith [habs.1, habs.2, hsource, hcost]

end RHTower.Sieve
