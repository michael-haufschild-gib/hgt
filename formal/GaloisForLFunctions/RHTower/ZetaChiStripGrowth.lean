import GaloisForLFunctions.RHTower.LPropertyStrips
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# Polynomial vertical growth of the functional-equation factor

`χ(s) = Γ_ℝ(1-s)/Γ_ℝ(s) = π^{s-1/2} Γ((1-s)/2)/Γ(s/2)`.  On a vertical strip and above height two
the sharp `Γ` decay and the matching `1/Γ` growth cancel their exponentials, leaving a power of the
height.  This is Titchmarsh IV.12.3 in the form Burnol's Lemma 4.10 consumes; `χ` has poles at
`s = 1, 3, 5, …`, all real, so no bound can hold on a full strip.

## Main results

* `norm_Gammaℝ_eq`
* `hasStripPolyGrowthOffReal_zetaChi`
-/

namespace RHTower

open Complex

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_Gammaℝ_eq (w : ℂ) :
    ‖Complex.Gammaℝ w‖ = Real.pi ^ (-w.re / 2) * ‖Complex.Gamma (w / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp

/-- **The modulus of the functional-equation factor.**  Off the real axis the `Γ_ℝ` quotient
splits into a power of `π` and a ratio of `Γ` moduli. -/
theorem norm_zetaChi_eq {s : ℂ} (hsim : s.im ≠ 0) :
    ‖zetaChi s‖ = Real.pi ^ (s.re - 1 / 2)
      * (‖Complex.Gamma ((1 - s) / 2)‖ * ‖(Complex.Gamma (s / 2))⁻¹‖) := by
  have hGne : Complex.Gamma (s / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m => ?_)
    intro hm
    have him0 : (s / 2).im = 0 := by
      rw [hm]
      simp
    have hh : (s / 2).im = s.im / 2 := by simp
    rw [hh] at him0
    exact hsim (by linarith)
  have hGpos : (0 : ℝ) < ‖Complex.Gamma (s / 2)‖ := norm_pos_iff.2 hGne
  have hppos : (0 : ℝ) < Real.pi ^ (-s.re / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hpow : Real.pi ^ (-(1 - s.re) / 2) / Real.pi ^ (-s.re / 2)
      = Real.pi ^ (s.re - 1 / 2) := by
    rw [← Real.rpow_sub Real.pi_pos]
    congr 1
    ring
  rw [zetaChi, norm_div, norm_Gammaℝ_eq, norm_Gammaℝ_eq, norm_inv]
  have hsre : (1 - s).re = 1 - s.re := by simp
  rw [hsre]
  calc Real.pi ^ (-(1 - s.re) / 2) * ‖Complex.Gamma ((1 - s) / 2)‖
        / (Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖)
      = (Real.pi ^ (-(1 - s.re) / 2) / Real.pi ^ (-s.re / 2))
        * (‖Complex.Gamma ((1 - s) / 2)‖ * ‖Complex.Gamma (s / 2)‖⁻¹) := by
        field_simp
    _ = Real.pi ^ (s.re - 1 / 2)
        * (‖Complex.Gamma ((1 - s) / 2)‖ * ‖Complex.Gamma (s / 2)‖⁻¹) := by rw [hpow]

/-- **Polynomial vertical growth of `χ` on every strip, above height two.** -/
theorem hasStripPolyGrowthOffReal_zetaChi : HasStripPolyGrowthOffReal zetaChi := by
  intro a b
  obtain ⟨C₁, N₁, hC₁, hb₁⟩ :=
    exists_sharp_bound_norm_Gamma_strip ((1 - b) / 2) ((1 - a) / 2)
  obtain ⟨C₂, N₂, hC₂, hb₂⟩ := exists_bound_norm_inv_Gamma_strip (a / 2) (b / 2)
  refine ⟨2, N₁ + N₂, Real.pi ^ (max (b - 1 / 2) 0) * (C₁ * C₂), by positivity,
    fun s h1 h2 h3 => ?_⟩
  have hτ : (2 : ℝ) ≤ |s.im| := h3
  have hhalf : (1 : ℝ) ≤ |s.im| / 2 := by linarith
  -- coordinates
  have hre1 : ((1 - s) / 2).re = (1 - s.re) / 2 := by simp
  have him1 : |((1 - s) / 2).im| = |s.im| / 2 := by
    have h : ((1 - s) / 2).im = -s.im / 2 := by simp
    rw [h, abs_div, abs_neg]
    norm_num
  have hre2 : (s / 2).re = s.re / 2 := by simp
  have him2 : |(s / 2).im| = |s.im| / 2 := by
    have h : (s / 2).im = s.im / 2 := by simp
    rw [h, abs_div]
    norm_num
  -- the two Gamma bounds
  have hG1 := hb₁ ((1 - s) / 2) (by rw [hre1]; linarith) (by rw [hre1]; linarith)
    (by rw [him1]; exact hhalf)
  rw [him1] at hG1
  have hG2 := hb₂ (s / 2) (by rw [hre2]; linarith) (by rw [hre2]; linarith)
    (by rw [him2]; exact hhalf)
  rw [him2] at hG2
  -- the modulus of chi
  have hsim : s.im ≠ 0 := by
    intro h
    rw [h] at hτ
    norm_num at hτ
  have hchi := norm_zetaChi_eq hsim
  rw [hchi]
  -- assemble
  have hexp : Real.exp (-(Real.pi * (|s.im| / 2) / 2)) * Real.exp (Real.pi * (|s.im| / 2) / 2)
      = 1 := by
    rw [← Real.exp_add]
    simp
  have hpi : Real.pi ^ (s.re - 1 / 2) ≤ Real.pi ^ (max (b - 1 / 2) 0) := by
    refine Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) ?_
    have := le_max_left (b - 1 / 2) (0 : ℝ)
    linarith
  have hprod : ‖Complex.Gamma ((1 - s) / 2)‖ * ‖(Complex.Gamma (s / 2))⁻¹‖
      ≤ C₁ * C₂ * (1 + |s.im|) ^ (N₁ + N₂) := by
    have hstep := mul_le_mul hG1 hG2 (norm_nonneg _) (by positivity)
    refine le_trans hstep ?_
    have hrw : (C₁ * (|s.im| / 2) ^ N₁ * Real.exp (-(Real.pi * (|s.im| / 2) / 2)))
        * (C₂ * (|s.im| / 2) ^ N₂ * Real.exp (Real.pi * (|s.im| / 2) / 2))
        = C₁ * C₂ * ((|s.im| / 2) ^ N₁ * (|s.im| / 2) ^ N₂) := by
      calc (C₁ * (|s.im| / 2) ^ N₁ * Real.exp (-(Real.pi * (|s.im| / 2) / 2)))
            * (C₂ * (|s.im| / 2) ^ N₂ * Real.exp (Real.pi * (|s.im| / 2) / 2))
          = C₁ * C₂ * ((|s.im| / 2) ^ N₁ * (|s.im| / 2) ^ N₂)
            * (Real.exp (-(Real.pi * (|s.im| / 2) / 2))
              * Real.exp (Real.pi * (|s.im| / 2) / 2)) := by ring
        _ = C₁ * C₂ * ((|s.im| / 2) ^ N₁ * (|s.im| / 2) ^ N₂) := by rw [hexp, mul_one]
    rw [hrw, ← pow_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    linarith [abs_nonneg s.im]
  have hnn : (0 : ℝ) ≤ ‖Complex.Gamma ((1 - s) / 2)‖ * ‖(Complex.Gamma (s / 2))⁻¹‖ := by
    positivity
  calc Real.pi ^ (s.re - 1 / 2)
        * (‖Complex.Gamma ((1 - s) / 2)‖ * ‖(Complex.Gamma (s / 2))⁻¹‖)
      ≤ Real.pi ^ (max (b - 1 / 2) 0) * (C₁ * C₂ * (1 + |s.im|) ^ (N₁ + N₂)) :=
        mul_le_mul hpi hprod hnn (by positivity)
    _ = Real.pi ^ (max (b - 1 / 2) 0) * (C₁ * C₂) * (1 + |s.im|) ^ (N₁ + N₂) := by ring

/-- **Burnol's Lemma 4.10, unconditional.**  The rapid-decrease class `𝓛¹` of Definition 12 is
stable under the functional-equation involution `F ↦ χ · F(1 - ·)`. -/
theorem hasStripRapidDecrease_zetaChi_mul_reflect {F : ℂ → ℂ}
    (hF : HasStripRapidDecrease F) :
    HasStripRapidDecrease (fun s => zetaChi s * F (1 - s)) :=
  hasStripRapidDecrease_chi_mul_reflect hF hasStripPolyGrowthOffReal_zetaChi

end

end RHTower
