import GaloisForLFunctions.RHTower.XiLogDerivVinogradovKorobovPositive
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivWidthBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegUniform
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRectangle

/-!
# `ζ'/ζ` on the Vinogradov–Korobov strip

With `w(t) = (log t)^{-2/3}(log log t)^{-5/3}/10⁸` (`vkHadamardWidth`):

* the region `1 - w(|γ|) < β` is zero-free for `|γ| ≥ T₀`, both signs of `γ`
  (`exists_vk_zero_free_region_abs`);
* `‖ζ'/ζ(σ+iγ)‖ ≤ C log|γ| / w(|γ|+1)` on `1 - w(|γ|+1)/2 ≤ σ ≤ 9/8`
  (`exists_logDeriv_zeta_bound_vk`, from `exists_logDeriv_zeta_bound_of_width`);
* uniformly on rectangles `|Im s| ≤ K`, `1 - min(δ, w(K+1))/2 ≤ Re s ≤ 9/8`: `ζ ≠ 0` there and
  `‖ζ'/ζ + 1/(s-1)‖ ≤ C log K / w(K+1)` (`exists_bound_zetaLogDerivReg_vk_uniform`).
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **The Vinogradov–Korobov region, both signs of the ordinate.** -/
theorem exists_vk_zero_free_region_abs :
    ∃ T₀ : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧ ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 →
      1 - RHTower.vkHadamardWidth |γ'| < β → riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨γ₀, hγ₀⟩ := riemannZeta_ne_zero_vinogradovKorobov
  refine ⟨max γ₀ (Real.exp (Real.exp 1)), le_max_right _ _, ?_⟩
  intro β γ' hγ' _ hβ hz
  have hγ₀' : γ₀ ≤ |γ'| := le_trans (le_max_left _ _) hγ'
  have hpos : riemannZeta ((β : ℂ) + ((|γ'| : ℝ) : ℂ) * Complex.I) = 0 := by
    rcases le_or_gt 0 γ' with h | h
    · rw [abs_of_nonneg h]; exact hz
    · have : (β : ℂ) + ((|γ'| : ℝ) : ℂ) * Complex.I
          = (starRingEnd ℂ) ((β : ℂ) + (γ' : ℂ) * Complex.I) := by
        rw [abs_of_neg h]; apply Complex.ext <;> simp
      rw [this, riemannZeta_conj, hz, map_zero]
  exact hγ₀ β |γ'| hγ₀' (by unfold RHTower.vkHadamardWidth at hβ; linarith) hpos

/-- The Vinogradov–Korobov threshold with `w ≤ 1/80`. -/
def vkLogDerivThreshold (T₀ : ℝ) : ℝ :=
  max (max T₀ 4) (Real.exp (max (Real.exp 1) ((10 ^ 8 * (1 / 80 : ℝ)) ^ (-(3 : ℝ) / 2))))

theorem vkWidth_props {T₀ : ℝ} (hT₀ : Real.exp (Real.exp 1) ≤ T₀) {t : ℝ}
    (ht : vkLogDerivThreshold T₀ ≤ t) :
    0 < RHTower.vkHadamardWidth t ∧ RHTower.vkHadamardWidth t ≤ 1 / 80 := by
  have h1 : Real.exp (Real.exp 1) ≤ t :=
    le_trans hT₀ (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht))
  have h2 : Real.exp (max (Real.exp 1) ((10 ^ 8 * (1 / 80 : ℝ)) ^ (-(3 : ℝ) / 2))) ≤ t :=
    le_trans (le_max_right _ _) ht
  exact ⟨RHTower.vkHadamardWidth_pos h1, RHTower.vkHadamardWidth_le (by norm_num) h2⟩

/-- **`ζ'/ζ` inside the Vinogradov–Korobov region.** -/
theorem exists_logDeriv_zeta_bound_vk :
    ∃ T₀ C : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧ 0 < C ∧
      (∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 → 1 - RHTower.vkHadamardWidth |γ'| < β →
        riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0) ∧
      ∀ σ γ : ℝ, vkLogDerivThreshold T₀ + 1 ≤ |γ| →
        1 - RHTower.vkHadamardWidth (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
          C * Real.log |γ| / RHTower.vkHadamardWidth (|γ| + 1) := by
  obtain ⟨T₀, hT₀, hreg⟩ := exists_vk_zero_free_region_abs
  set T₁ := vkLogDerivThreshold T₀ with hT₁
  have hT₁4 : (4 : ℝ) ≤ T₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT₁T₀ : T₀ ≤ T₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT₁e : Real.exp (Real.exp 1) ≤ T₁ := le_trans hT₀ hT₁T₀
  obtain ⟨C, hC0, hb⟩ := exists_logDeriv_zeta_bound_of_width (w := RHTower.vkHadamardWidth)
    (T₀ := T₁) hT₁4 (fun t ht => (vkWidth_props hT₀ ht).1) (fun t ht => (vkWidth_props hT₀ ht).2)
    (fun s t hs hst => RHTower.vkHadamardWidth_anti (le_trans hT₁e hs) hst)
    (fun β γ' hγ' hβ1 hβ => hreg β γ' (le_trans hT₁T₀ hγ') hβ1 hβ)
  exact ⟨T₀, C, hT₀, hC0, hreg, hb⟩

/-- The uniform contour width `min(δ, w(K+1))/2`. -/
def vkUniformRegWidth (δ K : ℝ) : ℝ := min δ (RHTower.vkHadamardWidth (K + 1)) / 2

/-- **The regular part on the Vinogradov–Korobov strip, uniformly in the height.** -/
theorem exists_bound_zetaLogDerivReg_vk_uniform :
    ∃ C δ K₀ : ℝ, 0 < C ∧ 0 < δ ∧ 3 ≤ K₀ ∧ Real.exp (Real.exp 1) ≤ K₀ ∧
      (∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
          1 - vkUniformRegWidth δ K ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0) ∧
      (∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
          1 - vkUniformRegWidth δ K ≤ s.re → s.re ≤ 9 / 8 →
          ‖zetaLogDerivReg s‖ ≤ C * Real.log K / RHTower.vkHadamardWidth (K + 1)) := by
  obtain ⟨T₀, C, hT₀, hC0, hreg, hb⟩ := exists_logDeriv_zeta_bound_vk
  set Θ := vkLogDerivThreshold T₀ with hΘ
  have hΘ4 : (4 : ℝ) ≤ Θ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hΘT₀ : T₀ ≤ Θ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hΘe : Real.exp (Real.exp 1) ≤ Θ := le_trans hT₀ hΘT₀
  obtain ⟨δ₁, hδ₁, M₀, hM₀, hbox⟩ :=
    exists_bound_zetaLogDerivReg_box 2 (Θ + 1) (by norm_num) (by linarith)
  obtain ⟨δ₂, hδ₂, hzfbox⟩ := exists_zero_free_box (Θ + 1)
  have hwpos : ∀ t, Θ ≤ t → 0 < RHTower.vkHadamardWidth t := fun t ht => (vkWidth_props hT₀ ht).1
  have hwle : ∀ t, Θ ≤ t → RHTower.vkHadamardWidth t ≤ 1 / 80 :=
    fun t ht => (vkWidth_props hT₀ ht).2
  have hwanti : ∀ s t, Θ ≤ s → s ≤ t → RHTower.vkHadamardWidth t ≤ RHTower.vkHadamardWidth s :=
    fun s t hs hst => RHTower.vkHadamardWidth_anti (le_trans hΘe hs) hst
  refine ⟨C + M₀ + 1, min δ₁ δ₂, max 3 (Θ + 1), by linarith, lt_min hδ₁ hδ₂, le_max_left _ _,
    le_trans hΘe (le_trans (by linarith) (le_max_right _ _)), ?_, ?_⟩
  · intro s K hK him hre hs1
    have hKΘ : Θ + 1 ≤ K := le_trans (le_max_right _ _) hK
    rcases le_or_gt 1 s.re with hre1 | hre1
    · exact riemannZeta_ne_zero_of_one_le_re hre1
    rcases le_or_gt (Θ + 1) |s.im| with hbig | hsmall
    · have hwK := hwanti (|s.im|) (K + 1) (by linarith) (by linarith)
      have hw1 := hwanti (|s.im|) (|s.im| + 1) (by linarith) (by linarith)
      have hwspos := hwpos (|s.im|) (by linarith)
      have hhalf : vkUniformRegWidth (min δ₁ δ₂) K ≤ RHTower.vkHadamardWidth (K + 1) / 2 := by
        unfold vkUniformRegWidth
        have := min_le_right (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1))
        linarith
      have hwK0 := hwpos (K + 1) (by linarith)
      have hedge : 1 - RHTower.vkHadamardWidth |s.im| < s.re := by linarith
      have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im s).symm
      rw [hsplit]
      exact hreg s.re s.im (by linarith) hre1.le hedge
    · have hδcmp : vkUniformRegWidth (min δ₁ δ₂) K ≤ δ₂ := by
        unfold vkUniformRegWidth
        have := min_le_left (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1))
        have := min_le_right δ₁ δ₂
        have : 0 ≤ min δ₁ δ₂ := le_of_lt (lt_min hδ₁ hδ₂)
        linarith
      exact hzfbox s (by linarith) hre1.le hsmall.le hs1
  · intro s K hK him hre hhi
    have hK3 : (3 : ℝ) ≤ K := le_trans (le_max_left _ _) hK
    have hKΘ : Θ + 1 ≤ K := le_trans (le_max_right _ _) hK
    have hwKpos := hwpos (K + 1) (by linarith)
    have hwKle := hwle (K + 1) (by linarith)
    have hlogK : (1 : ℝ) ≤ Real.log K := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      linarith
    have hratio : (1 : ℝ) ≤ Real.log K / RHTower.vkHadamardWidth (K + 1) := by
      rw [le_div_iff₀ hwKpos]; linarith
    have hexp : (C + M₀ + 1) * Real.log K / RHTower.vkHadamardWidth (K + 1)
        = C * Real.log K / RHTower.vkHadamardWidth (K + 1)
          + (M₀ + 1) * (Real.log K / RHTower.vkHadamardWidth (K + 1)) := by
      field_simp; ring
    have hfinal : (M₀ + 1) * 1 ≤ (M₀ + 1) * (Real.log K / RHTower.vkHadamardWidth (K + 1)) :=
      mul_le_mul_of_nonneg_left hratio (by linarith)
    rcases le_or_gt (Θ + 1) |s.im| with hbig | hsmall
    · have him4 : (4 : ℝ) ≤ |s.im| := by linarith
      have hwmono := hwanti (|s.im| + 1) (K + 1) (by linarith) (by linarith)
      have hwspos := hwpos (|s.im| + 1) (by linarith)
      have hhalf : vkUniformRegWidth (min δ₁ δ₂) K ≤ RHTower.vkHadamardWidth (K + 1) / 2 := by
        unfold vkUniformRegWidth
        have := min_le_right (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1))
        linarith
      have hwide : 1 - RHTower.vkHadamardWidth (|s.im| + 1) / 2 ≤ s.re := by linarith
      have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im s).symm
      have hres : ‖logDeriv riemannZeta s‖
          ≤ C * Real.log |s.im| / RHTower.vkHadamardWidth (|s.im| + 1) := by
        have h := hb s.re s.im hbig hwide hhi
        rwa [← hsplit] at h
      have hs1 : s ≠ 1 := by
        intro h; rw [h] at him4; simp only [Complex.one_im, abs_zero] at him4; linarith
      have hzeta : riemannZeta s ≠ 0 := by
        rcases le_or_gt 1 s.re with hre1 | hre1
        · exact riemannZeta_ne_zero_of_one_le_re hre1
        · have hw2 := hwanti (|s.im|) (|s.im| + 1) (by linarith) (by linarith)
          have hwpos' := hwpos (|s.im|) (by linarith)
          have hedge : 1 - RHTower.vkHadamardWidth |s.im| < s.re := by linarith
          rw [hsplit]
          exact hreg s.re s.im (by linarith) hre1.le hedge
      have hdecomp := neg_logDeriv_riemannZeta_eq_of_ne_zero hs1 hzeta
      have hpole : ‖(s - 1)⁻¹‖ ≤ 1 / 4 := by
        rw [norm_inv]
        have hge : (4 : ℝ) ≤ ‖s - 1‖ := by
          have h := Complex.abs_im_le_norm (s - 1)
          simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
          linarith
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have hregb : ‖zetaLogDerivReg s‖ ≤ ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by
        have heq : zetaLogDerivReg s = -(logDeriv riemannZeta s) - (s - 1)⁻¹ := by
          rw [hdecomp]; ring
        rw [heq]
        calc ‖-(logDeriv riemannZeta s) - (s - 1)⁻¹‖
            ≤ ‖-(logDeriv riemannZeta s)‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
          _ = ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by rw [norm_neg]
      have hlogle : Real.log |s.im| ≤ Real.log K := Real.log_le_log (by linarith) him
      have hlognn : (0 : ℝ) ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
      have htransfer : C * Real.log |s.im| / RHTower.vkHadamardWidth (|s.im| + 1)
          ≤ C * Real.log K / RHTower.vkHadamardWidth (K + 1) := by
        refine div_le_div_of_nonneg_left ?_ hwKpos hwmono |>.trans ?_
        · positivity
        · exact div_le_div_of_nonneg_right (by nlinarith) hwKpos.le
      rw [hexp]
      linarith
    · have hδcmp : vkUniformRegWidth (min δ₁ δ₂) K ≤ δ₁ := by
        unfold vkUniformRegWidth
        have := min_le_left (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1))
        have := min_le_left δ₁ δ₂
        have : 0 ≤ min δ₁ δ₂ := le_of_lt (lt_min hδ₁ hδ₂)
        linarith
      have hres := hbox s (by linarith) (by linarith) hsmall.le
      have hCnn : (0 : ℝ) ≤ C * Real.log K / RHTower.vkHadamardWidth (K + 1) := by positivity
      rw [hexp]
      linarith

end

end RHTower.Sieve
