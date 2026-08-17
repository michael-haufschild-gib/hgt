import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivWidthBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegUniform
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorRouteTZeroFree

/-!
# The regular part on the Route-T strip, uniformly in the height

The exponent-one strip carries `‖zetaLogDerivReg‖ ≤ C log²K` on width `≍ 1/log K`.  Running the same
argument against the Vinogradov-type Route-T width gives the wider strip

```text
1 - w(K+1)/2 ≤ σ ≤ 9/8 ,  |γ| ≤ K   ⟹   ‖zetaLogDerivReg(σ+iγ)‖ ≤ C·log K / w(K+1),
```

with `w = routeTZeroFreeWidth`, whose reciprocal is `O((log K)^{9/10}(log log K)²)` rather than
`O(log K)`.  A contour placed on that abscissa saves `N^{-w}` instead of `N^{-c/log K}`.

Both halves are pinned to the same zero-free region, so the width in the bound and the width in the
hypothesis are the same object: the region is obtained once and fed to the Landau argument, rather
than each being produced by its own existential.

Below the Route-T threshold the strip meets a compact box, where the regular part is bounded by
compactness alone — the pole costing nothing, since `zetaLogDerivReg` is regular at `1`.
-/

namespace RHTower.Sieve

open Complex

/-- The contour width at parameter `K`: half the smaller of the compact-box margin and the Route-T
zero-free width one unit above `K`. -/
noncomputable def routeTUniformRegWidth (A delta K : ℝ) : ℝ :=
  min delta (routeTZeroFreeWidth A (K + 1)) / 2

theorem routeTUniformRegWidth_pos {A delta K : ℝ} (hdelta : 0 < delta) :
    0 < routeTUniformRegWidth A delta K :=
  div_pos (lt_min hdelta (routeTZeroFreeWidth_pos A (K + 1))) (by norm_num)

theorem routeTUniformRegWidth_le_delta {A delta K : ℝ} (hdelta : 0 < delta) :
    routeTUniformRegWidth A delta K ≤ delta := by
  unfold routeTUniformRegWidth
  have h := min_le_left delta (routeTZeroFreeWidth A (K + 1))
  linarith

theorem routeTUniformRegWidth_le_half {A delta K : ℝ} :
    routeTUniformRegWidth A delta K ≤ routeTZeroFreeWidth A (K + 1) / 2 := by
  unfold routeTUniformRegWidth
  have h := min_le_right delta (routeTZeroFreeWidth A (K + 1))
  linarith

/-- The Route-T width is at most `1/160`, so `log K` past `3` already dominates its reciprocal. -/
theorem routeTZeroFreeWidth_le_one_sixtieth (A γ : ℝ) :
    routeTZeroFreeWidth A γ ≤ 1 / 160 := by
  have h := routeTZeroFreeDelta_le_sixteenth A γ
  unfold routeTZeroFreeWidth
  linarith

/-- **`ζ'/ζ` inside a given Route-T zero-free region.**  The region is an input rather than an
existential, so the width in the conclusion is the width of that same region. -/
theorem exists_logDeriv_zeta_bound_routeT_of_region {A : ℝ}
    (hA : ∀ β γ : ℝ, 100000 ≤ |γ| →
      routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight |γ| → β ≤ 1 →
      1 - routeTZeroFreeWidth A |γ| < β →
      riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ γ : ℝ, routeTLogDerivThreshold + 1 ≤ |γ| →
        1 - routeTZeroFreeWidth A (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| / routeTZeroFreeWidth A (|γ| + 1) := by
  have hbase := routeTLogDerivThreshold_ge
  have hT₀4 : (4 : ℝ) ≤ routeTLogDerivThreshold := by linarith
  have hpi : (8 : ℝ) * Real.pi + 1 ≤ routeTLogDerivThreshold := by
    have hp := Real.pi_le_four
    linarith
  obtain ⟨C, hC0, hb⟩ :=
    exists_logDeriv_zeta_bound_of_width (w := fun t => routeTZeroFreeWidth A t)
      (T₀ := routeTLogDerivThreshold) hT₀4
      (fun t _ => routeTZeroFreeWidth_pos A t)
      (fun t _ => by
        have hd := routeTZeroFreeDelta_le_sixteenth A t
        show routeTZeroFreeWidth A t ≤ 1 / 80
        unfold routeTZeroFreeWidth
        linarith)
      (fun s t hs hst => routeTZeroFreeWidth_antitone (le_trans hpi hs) hst)
      (fun β γ' hγ' hβ1 hβgt =>
        hA β γ' (le_trans hbase hγ')
          (routeTBinaryHeight_ge_of_threshold hγ') hβ1 hβgt)
  exact ⟨C, hC0, hb⟩

/-- **The regular part on the Route-T strip, uniformly up to height `K`**, together with the
zero-free statement for the same strip.  Both are read off a single region. -/
theorem exists_bound_zetaLogDerivReg_routeT_uniform :
    ∃ A C delta K₀ : ℝ, 0 < C ∧ 0 < delta ∧ 3 ≤ K₀ ∧
      (∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
          1 - routeTUniformRegWidth A delta K ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0) ∧
      (∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
          1 - routeTUniformRegWidth A delta K ≤ s.re → s.re ≤ 9 / 8 →
          ‖zetaLogDerivReg s‖ ≤ C * Real.log K / routeTZeroFreeWidth A (K + 1)) := by
  obtain ⟨A, hA⟩ := exists_routeT_zero_free_region_abs
  obtain ⟨C, hC0, hb⟩ := exists_logDeriv_zeta_bound_routeT_of_region hA
  obtain ⟨δ₁, hδ₁, M₀, hM₀, hbox⟩ :=
    exists_bound_zetaLogDerivReg_box 2 (routeTLogDerivThreshold + 1) (by norm_num)
      (by linarith [routeTLogDerivThreshold_ge])
  obtain ⟨δ₂, hδ₂, hzfbox⟩ := exists_zero_free_box (routeTLogDerivThreshold + 1)
  have hbase := routeTLogDerivThreshold_ge
  have hpi : (8 : ℝ) * Real.pi + 1 ≤ routeTLogDerivThreshold + 1 := by
    have hp := Real.pi_le_four
    linarith
  refine ⟨A, C + M₀ + 1, min δ₁ δ₂, max 3 (routeTLogDerivThreshold + 1), by linarith,
    lt_min hδ₁ hδ₂, le_max_left _ _, ?_, ?_⟩
  · -- the zero-free half
    intro s K hK him hre hs1
    have hK3 : (3 : ℝ) ≤ K := le_trans (le_max_left _ _) hK
    have hKΘ : routeTLogDerivThreshold + 1 ≤ K := le_trans (le_max_right _ _) hK
    rcases le_or_gt 1 s.re with hre1 | hre1
    · exact riemannZeta_ne_zero_of_one_le_re hre1
    rcases le_or_gt (routeTLogDerivThreshold + 1) |s.im| with hbig | hsmall
    · have him0 : (100000 : ℝ) ≤ |s.im| := by linarith
      have hwmono : routeTZeroFreeWidth A (K + 1) ≤ routeTZeroFreeWidth A (|s.im| + 1) :=
        routeTZeroFreeWidth_antitone (le_trans hpi (by linarith)) (by linarith)
      have hw2 : routeTZeroFreeWidth A (|s.im| + 1) ≤ routeTZeroFreeWidth A |s.im| :=
        routeTZeroFreeWidth_antitone (le_trans hpi (by linarith)) (by linarith)
      have hwpos : 0 < routeTZeroFreeWidth A |s.im| := routeTZeroFreeWidth_pos A _
      have hhalf := routeTUniformRegWidth_le_half (A := A) (delta := min δ₁ δ₂) (K := K)
      have hedge : 1 - routeTZeroFreeWidth A |s.im| < s.re := by linarith
      have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im s).symm
      rw [hsplit]
      exact hA s.re s.im him0 (routeTBinaryHeight_ge_of_threshold (by linarith)) hre1.le hedge
    · have hδcmp : routeTUniformRegWidth A (min δ₁ δ₂) K ≤ δ₂ :=
        le_trans (routeTUniformRegWidth_le_delta (lt_min hδ₁ hδ₂)) (min_le_right _ _)
      exact hzfbox s (by linarith) hre1.le hsmall.le hs1
  · -- the size half
    intro s K hK him hre hhi
    have hK3 : (3 : ℝ) ≤ K := le_trans (le_max_left _ _) hK
    have hKΘ : routeTLogDerivThreshold + 1 ≤ K := le_trans (le_max_right _ _) hK
    have hwKpos : 0 < routeTZeroFreeWidth A (K + 1) := routeTZeroFreeWidth_pos A _
    have hwKle : routeTZeroFreeWidth A (K + 1) ≤ 1 / 160 :=
      routeTZeroFreeWidth_le_one_sixtieth A _
    have hlogK : (1 : ℝ) ≤ Real.log K := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      linarith
    have hratio : (1 : ℝ) ≤ Real.log K / routeTZeroFreeWidth A (K + 1) := by
      rw [le_div_iff₀ hwKpos]
      linarith
    rcases le_or_gt (routeTLogDerivThreshold + 1) |s.im| with hbig | hsmall
    · have him4 : (4 : ℝ) ≤ |s.im| := by linarith
      have him0 : (100000 : ℝ) ≤ |s.im| := by linarith
      have hwmono : routeTZeroFreeWidth A (K + 1) ≤ routeTZeroFreeWidth A (|s.im| + 1) :=
        routeTZeroFreeWidth_antitone (le_trans hpi (by linarith)) (by linarith)
      have hwspos : 0 < routeTZeroFreeWidth A (|s.im| + 1) := routeTZeroFreeWidth_pos A _
      have hhalf := routeTUniformRegWidth_le_half (A := A) (delta := min δ₁ δ₂) (K := K)
      have hwide : 1 - routeTZeroFreeWidth A (|s.im| + 1) / 2 ≤ s.re := by linarith
      have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im s).symm
      have hres : ‖logDeriv riemannZeta s‖
          ≤ C * Real.log |s.im| / routeTZeroFreeWidth A (|s.im| + 1) := by
        have h := hb s.re s.im hbig hwide hhi
        rwa [← hsplit] at h
      have hs1 : s ≠ 1 := by
        intro h
        rw [h] at him4
        simp only [Complex.one_im, abs_zero] at him4
        linarith
      have hzeta : riemannZeta s ≠ 0 := by
        rcases le_or_gt 1 s.re with hre1 | hre1
        · exact riemannZeta_ne_zero_of_one_le_re hre1
        · have hw2 : routeTZeroFreeWidth A (|s.im| + 1) ≤ routeTZeroFreeWidth A |s.im| :=
            routeTZeroFreeWidth_antitone (le_trans hpi (by linarith)) (by linarith)
          have hwpos : 0 < routeTZeroFreeWidth A |s.im| := routeTZeroFreeWidth_pos A _
          have hedge : 1 - routeTZeroFreeWidth A |s.im| < s.re := by linarith
          rw [hsplit]
          exact hA s.re s.im him0 (routeTBinaryHeight_ge_of_threshold (by linarith)) hre1.le hedge
      have hzu : zetaResidueUnit s ≠ 0 := (zetaResidueUnit_ne_zero_iff hs1).2 hzeta
      have hdecomp : -(logDeriv riemannZeta s) = (s - 1)⁻¹ + zetaLogDerivReg s :=
        neg_logDeriv_riemannZeta_eq hs1 hzu
      have hpole : ‖(s - 1)⁻¹‖ ≤ 1 / 4 := by
        rw [norm_inv]
        have hge : (4 : ℝ) ≤ ‖s - 1‖ := by
          have h := Complex.abs_im_le_norm (s - 1)
          simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
          linarith
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have hreg : ‖zetaLogDerivReg s‖ ≤ ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by
        have heq : zetaLogDerivReg s = -(logDeriv riemannZeta s) - (s - 1)⁻¹ := by
          rw [hdecomp]; ring
        rw [heq]
        calc ‖-(logDeriv riemannZeta s) - (s - 1)⁻¹‖
            ≤ ‖-(logDeriv riemannZeta s)‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
          _ = ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by rw [norm_neg]
      have hlogle : Real.log |s.im| ≤ Real.log K := Real.log_le_log (by linarith) him
      have hlognn : (0 : ℝ) ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
      have htransfer : C * Real.log |s.im| / routeTZeroFreeWidth A (|s.im| + 1)
          ≤ C * Real.log K / routeTZeroFreeWidth A (K + 1) := by
        refine div_le_div_of_nonneg_left ?_ hwKpos hwmono |>.trans ?_
        · positivity
        · exact div_le_div_of_nonneg_right (by nlinarith) hwKpos.le
      have hfinal : (M₀ + 1) * 1 ≤ (M₀ + 1) * (Real.log K / routeTZeroFreeWidth A (K + 1)) :=
        mul_le_mul_of_nonneg_left hratio (by linarith)
      have hexp : (C + M₀ + 1) * Real.log K / routeTZeroFreeWidth A (K + 1)
          = C * Real.log K / routeTZeroFreeWidth A (K + 1)
            + (M₀ + 1) * (Real.log K / routeTZeroFreeWidth A (K + 1)) := by
        field_simp
        ring
      rw [hexp]
      linarith
    · have hδcmp : routeTUniformRegWidth A (min δ₁ δ₂) K ≤ δ₁ :=
        le_trans (routeTUniformRegWidth_le_delta (lt_min hδ₁ hδ₂)) (min_le_left _ _)
      have hres := hbox s (by linarith) (by linarith) hsmall.le
      have hfinal : (M₀ + 1) * 1 ≤ (M₀ + 1) * (Real.log K / routeTZeroFreeWidth A (K + 1)) :=
        mul_le_mul_of_nonneg_left hratio (by linarith)
      have hCnn : (0 : ℝ) ≤ C * Real.log K / routeTZeroFreeWidth A (K + 1) := by positivity
      have hexp : (C + M₀ + 1) * Real.log K / routeTZeroFreeWidth A (K + 1)
          = C * Real.log K / routeTZeroFreeWidth A (K + 1)
            + (M₀ + 1) * (Real.log K / routeTZeroFreeWidth A (K + 1)) := by
        field_simp
        ring
      rw [hexp]
      linarith

end RHTower.Sieve
