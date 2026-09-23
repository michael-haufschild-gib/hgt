import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegLowBox
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegionBound
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRegionKappaOne

/-!
# The regular part on the width-`1/log` strip, uniformly in the height

Unlike `1/ζ`, the regular part of `-ζ'/ζ` is bounded by `C log²|γ|` on the **full width** of the
exponent-one zero-free region:

```text
1 - (1/40000)/log|γ| ≤ σ ≤ 9/8   ⟹   ‖zetaLogDerivReg(σ+iγ)‖ ≤ C log²|γ|.
```

That estimate has an astronomical height threshold, and below it the strip meets a compact box on
which the regular part — analytic there, the pole costing nothing — is bounded by compactness.
Fitting the two gives a bound with no height restriction, and with the strip pinned to a contour
parameter `K` rather than to the height of `s`.

Width `≍ 1/log K` is the reason a Chebyshev contour can save more than a Möbius contour, which
needs `1/ζ` and hence a strip of width only `log^{-2}K`.
-/

namespace RHTower.Sieve

open Complex

/-- **The regular part is bounded on a box of arbitrary height.**  Compactness plus analyticity;
the constant depends on the height but carries no rate. -/
theorem exists_bound_zetaLogDerivReg_box (d T : ℝ) (hd : 1 ≤ d) (hT : 0 ≤ T) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ d → |s.im| ≤ T → ‖zetaLogDerivReg s‖ ≤ M := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect (T := T) hT
  refine ⟨δ, hδ, ?_⟩
  set c : ℝ := 1 - δ with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  have hcd : c ≤ d := le_trans hc1 hd
  have hrect : Set.uIcc c d ×ℂ Set.uIcc (-T) T = Set.Icc c d ×ℂ Set.Icc (-T) T := by
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
  have hdiff : DifferentiableOn ℂ zetaLogDerivReg (Set.Icc c d ×ℂ Set.Icc (-T) T) := by
    rw [← hrect]
    exact differentiableOn_zetaLogDerivReg_rect (hzf c d (by rw [hcdef]) hc1 hd)
  have hK : IsCompact (Set.Icc c d ×ℂ Set.Icc (-T) T) := isCompact_reProdIm_Icc _ _ _ _
  have hne : (Set.Icc c d ×ℂ Set.Icc (-T) T).Nonempty := by
    refine ⟨1, ⟨by simpa using hc1, by simpa using hd⟩, ?_, ?_⟩
    · simp only [Complex.one_im]; linarith
    · simp only [Complex.one_im]; linarith
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hdiff.continuousOn.norm)
  refine ⟨‖zetaLogDerivReg z‖, norm_nonneg _, fun s hlo hhi him => ?_⟩
  exact hmax (show s ∈ Set.Icc c d ×ℂ Set.Icc (-T) T from
    ⟨⟨hlo, hhi⟩, (abs_le.1 him).1, (abs_le.1 him).2⟩)

/-- Three is past `e`. -/
theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : Real.log (Real.exp 1) < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
  rw [Real.log_exp] at h1
  linarith

/-- **The width-`1/log` strip is zero-free, uniformly up to height `K`.** -/
theorem exists_zeta_uniform_kappa_one_zero_free :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (s : ℂ) (K : ℝ), L₀ ≤ Real.log K → |s.im| ≤ K →
      1 - 1 / 40000 / Real.log K ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨T, hT3, hregion⟩ := exists_zero_free_region_explicit
  obtain ⟨δ, hδ0, hbox⟩ := exists_zero_free_box T
  refine ⟨max 1 (1 / 40000 / δ), le_max_left _ _, ?_⟩
  intro s K hL hKim hre hne
  have hL1 : (1 : ℝ) ≤ Real.log K := le_trans (le_max_left _ _) hL
  have hLδ : 1 / 40000 / δ ≤ Real.log K := le_trans (le_max_right _ _) hL
  rcases le_or_gt 1 s.re with hx1 | hx1
  · exact riemannZeta_ne_zero_of_one_le_re hx1
  rcases le_or_gt T |s.im| with hbig | hsmall
  · have habs3 : (3 : ℝ) ≤ |s.im| := le_trans hT3 hbig
    have hlog1 : (1 : ℝ) ≤ Real.log |s.im| :=
      le_trans one_le_log_three (Real.log_le_log (by norm_num) habs3)
    have hpos : (0 : ℝ) < Real.log |s.im| := by linarith
    have hlt : Real.log |s.im| ≤ Real.log K := Real.log_le_log (by linarith) hKim
    have h1 : 1 / 40000 / Real.log K ≤ 1 / 40000 / Real.log |s.im| :=
      div_le_div_of_nonneg_left (by norm_num) hpos hlt
    have h2 : 1 / 40000 / Real.log |s.im| < 1 / 10000 / Real.log |s.im| := by
      have heq : 1 / 10000 / Real.log |s.im| - 1 / 40000 / Real.log |s.im|
          = 3 / 40000 / Real.log |s.im| := by ring
      have hp : (0 : ℝ) < 3 / 40000 / Real.log |s.im| := div_pos (by norm_num) hpos
      linarith [heq, hp]
    have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im s).symm
    rw [hsplit]
    exact hregion s.re s.im hbig hx1.le (by linarith)
  · have hδcmp : 1 / 40000 / Real.log K ≤ δ := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log K)]
      rw [div_le_iff₀ hδ0] at hLδ
      nlinarith [hLδ]
    exact hbox s (by linarith) hx1.le (le_of_lt hsmall) hne

/-- **The regular part on the strip, uniformly up to height `K`.** -/
theorem exists_bound_zetaLogDerivReg_uniform :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ (s : ℂ) (K : ℝ), L₀ ≤ Real.log K → |s.im| ≤ K →
      1 - 1 / 40000 / Real.log K ≤ s.re → s.re ≤ 9 / 8 →
      ‖zetaLogDerivReg s‖ ≤ C * Real.log K ^ (2 : ℕ) := by
  obtain ⟨C₁, T, hC₁0, hT4, hbound⟩ := exists_logDeriv_zeta_bound_explicit
  obtain ⟨δ, hδ0, M₀, hM₀0, hbox⟩ :=
    exists_bound_zetaLogDerivReg_box 2 T (by norm_num) (by linarith)
  obtain ⟨L₁, hL₁1, hzf⟩ := exists_zeta_uniform_kappa_one_zero_free
  refine ⟨C₁ + M₀ + 1, max (max 1 (1 / 40000 / δ)) L₁, by linarith,
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro s K hL hKim hre hhi
  have hL1 : (1 : ℝ) ≤ Real.log K :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL)
  have hLδ : 1 / 40000 / δ ≤ Real.log K :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hL)
  have hL₁K : L₁ ≤ Real.log K := le_trans (le_max_right _ _) hL
  have hLsq : (1 : ℝ) ≤ Real.log K ^ (2 : ℕ) := by nlinarith
  rcases le_or_gt T |s.im| with hbig | hsmall
  · -- the region branch, with the pole term split off
    have habs4 : (4 : ℝ) ≤ |s.im| := le_trans hT4 hbig
    have hlog1 : (1 : ℝ) ≤ Real.log |s.im| := one_le_log_abs habs4
    have hlt : Real.log |s.im| ≤ Real.log K := Real.log_le_log (by linarith) hKim
    have hwide : 1 - 1 / 40000 / Real.log |s.im| ≤ s.re := by
      have h1 : 1 / 40000 / Real.log K ≤ 1 / 40000 / Real.log |s.im| :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) hlt
      linarith
    have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im s).symm
    have hres : ‖logDeriv riemannZeta s‖ ≤ C₁ * Real.log |s.im| ^ (2 : ℕ) := by
      have h := hbound s.re s.im hbig hwide hhi
      rwa [← hsplit] at h
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at habs4
      simp only [Complex.one_im, abs_zero] at habs4
      linarith
    have hzu : zetaResidueUnit s ≠ 0 :=
      (zetaResidueUnit_ne_zero_iff hs1).2 (hzf s K hL₁K hKim hre hs1)
    have hdecomp : -(logDeriv riemannZeta s) = (s - 1)⁻¹ + zetaLogDerivReg s :=
      neg_logDeriv_riemannZeta_eq hs1 hzu
    have hpole : ‖(s - 1)⁻¹‖ ≤ 1 / 4 := by
      rw [norm_inv]
      have hge : (4 : ℝ) ≤ ‖s - 1‖ := by
        have h := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
        linarith [habs4, h]
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hreg : ‖zetaLogDerivReg s‖ ≤ ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by
      have heq : zetaLogDerivReg s = -(logDeriv riemannZeta s) - (s - 1)⁻¹ := by
        rw [hdecomp]; ring
      rw [heq]
      calc ‖-(logDeriv riemannZeta s) - (s - 1)⁻¹‖
          ≤ ‖-(logDeriv riemannZeta s)‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
        _ = ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by rw [norm_neg]
    have hpow : Real.log |s.im| ^ (2 : ℕ) ≤ Real.log K ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by linarith) hlt 2
    nlinarith [hres, hpole, hreg, hpow, hLsq, hM₀0, hC₁0]
  · -- the compact branch
    have hδcmp : 1 / 40000 / Real.log K ≤ δ := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log K)]
      rw [div_le_iff₀ hδ0] at hLδ
      nlinarith [hLδ]
    have hres := hbox s (by linarith) (by linarith) (le_of_lt hsmall)
    nlinarith [hres, hLsq, hC₁0, hM₀0]

end RHTower.Sieve
