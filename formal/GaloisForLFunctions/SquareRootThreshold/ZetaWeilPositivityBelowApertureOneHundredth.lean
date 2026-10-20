import GaloisForLFunctions.SquareRootThreshold.NegativityRateEqualsMaximalDepth

/-!
# Weil positivity of `ζ` below aperture `1/100`

Every `C²` test supported in `[−1/100, 1/100]` has `Re W_ζ(f, f) ≥ ‖f‖²/25`
(`zetaZeroConfig_re_W_ge_of_aperture_le_hundredth`). The earlier unconditional aperture was
`e^{−50}` (`zetaZeroConfig_re_W_nonneg_of_small_aperture`).

Below aperture `(log 2)/2` the explicit formula has no prime terms. The pole terms cost
`2(sinh a − a)‖f‖² ≤ 2a²‖f‖²`. Everything else rests on the archimedean density
`μ(τ) = (Re ψ(¼ + iτ/2) − log π)/(2π)`:

* **High frequencies** (`mu_ge_log_abs`). For `|τ| ≥ 4`, `Re ψ(¼ + iτ/2) ≥ log(|τ|/2) − 6/|τ|` by
  `|ψ(z) − log z| ≤ 3/|z|`. So `μ(τ) ≥ (log|τ| − log 2π − 6/|τ|)/(2π)`.
* **Low frequencies** (`mu_ge_neg`). `μ(τ) ≥ −(7 + log π)/(2π)` for every `τ`.
* **Spectral mass.** `|h_f(τ)|² ≤ 2a‖f‖²`, so `[−R, R]` carries at most `4aR‖f‖²` of the total
  `2π‖f‖²` (`integral_norm_sq_paperFT_mul_mu_ge_three_band`).

With `R = π/(4a)` the archimedean term is at least
`(½(log(1/(4πa)) − 3/2 − 24a/π) − (8a/π)(log 2 + 11/2))‖f‖²`. Since `log(25/π) > 2`, this is
positive for `a ≤ 1/100`. Height-window positivity follows for windows of aperture `1/100`
(`re_windowedW_zetaZeroConfig_nonneg_of_hundredth`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- `Re ψ(¼ + iτ/2) ≥ log(|τ|/2) − 6/|τ|` for `|τ| ≥ 4`. -/
theorem re_digamma_quarter_ge {τ : ℝ} (hτ : 4 ≤ |τ|) :
    Real.log (|τ| / 2) - 6 / |τ| ≤ (Complex.digamma (1 / 4 + I * τ / 2)).re := by
  set z : ℂ := 1 / 4 + I * τ / 2 with hz
  have hzre : z.re = 1 / 4 := by simp [hz]
  have hzim : z.im = τ / 2 := by simp [hz]
  have hn : |τ| / 2 ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    exact this
  have hbound := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos (z := z)
    (by rw [hzre]; norm_num) (by linarith)
  have hre_dig : Real.log ‖z‖ - 3 / ‖z‖ ≤ (Complex.digamma z).re := by
    have h := Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)
    rw [Complex.sub_re, Complex.log_re] at h
    have := neg_abs_le ((Complex.digamma z).re - Real.log ‖z‖)
    linarith
  have hlog : Real.log (|τ| / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by positivity) hn
  have h3 : 3 / ‖z‖ ≤ 6 / |τ| := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  linarith

theorem mu_eq_re_digamma (τ : ℝ) :
    mu τ = ((Complex.digamma (1 / 4 + I * τ / 2)).re - Real.log π) / (2 * π) := by
  unfold mu
  field_simp

/-- High frequencies: `μ(τ) ≥ (log|τ| − log 2π − 6/|τ|)/(2π)` for `|τ| ≥ 4`. -/
theorem mu_ge_log_abs {τ : ℝ} (hτ : 4 ≤ |τ|) :
    (Real.log |τ| - Real.log (2 * π) - 6 / |τ|) / (2 * π) ≤ mu τ := by
  rw [mu_eq_re_digamma, div_le_div_iff_of_pos_right (by positivity)]
  have h := re_digamma_quarter_ge hτ
  have h1 : Real.log (|τ| / 2) = Real.log |τ| - Real.log 2 :=
    Real.log_div (by linarith) two_ne_zero
  have h2 : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul two_ne_zero Real.pi_ne_zero
  linarith

/-- Low frequencies: `μ(τ) ≥ −(7 + log π)/(2π)` for every `τ`. -/
theorem mu_ge_neg (τ : ℝ) : -(7 + Real.log π) / (2 * π) ≤ mu τ := by
  rw [mu_eq_re_digamma, div_le_div_iff_of_pos_right (by positivity)]
  have h := log_sub_seven_le_re_digamma_quarter τ
  have : 0 ≤ Real.log (1 + |τ| / 4) := Real.log_nonneg (by linarith [abs_nonneg τ])
  linarith

/-- The high-frequency floor `(log R − log 2π − 6/R)/(2π)` of the archimedean density. -/
def muHigh (R : ℝ) : ℝ := (Real.log R - Real.log (2 * π) - 6 / R) / (2 * π)

/-- The floor `(log 4 − log 2π − 3/2)/(2π)` on `|τ| ≥ 4`. -/
def muMid : ℝ := (Real.log 4 - Real.log (2 * π) - 3 / 2) / (2 * π)

/-- The floor `−(7 + log π)/(2π)` on all of `ℝ`. -/
def muLow : ℝ := -(7 + Real.log π) / (2 * π)

theorem muMid_le_muHigh {R : ℝ} (hR : 4 ≤ R) : muMid ≤ muHigh R := by
  rw [muMid, muHigh, div_le_div_iff_of_pos_right (by positivity)]
  have h1 : Real.log 4 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have h2 : 6 / R ≤ 3 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

theorem muLow_le_muMid : muLow ≤ muMid := by
  rw [muMid, muLow, div_le_div_iff_of_pos_right (by positivity)]
  have h2 : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul two_ne_zero Real.pi_ne_zero
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/-- **The archimedean term in three bands.** For a `C²` test supported in `[−a, a]` and `R ≥ 4`,
`∫ |h_f|² μ ≥ (2π μ_H − 4aR(μ_H − μ_M) − 16a(μ_M − μ_L)) ‖f‖²`. -/
theorem integral_norm_sq_paperFT_mul_mu_ge_three_band {a R : ℝ} (ha : 0 ≤ a) (hR : 4 ≤ R)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    (2 * π * muHigh R - 4 * a * R * (muHigh R - muMid) - 16 * a * (muMid - muLow)) *
      ∫ t, ‖f t‖ ^ 2 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * mu τ := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hval : ∀ τ : ℝ, paperFT (EF.weilTest f f) τ = ((‖paperFT f τ‖ ^ 2 : ℝ) : ℂ) :=
    paperFT_weilTest_self_ofReal hf.continuous hfc
  have hint_mu : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * mu τ := by
    refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have hint_sq : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 := by
    refine (EF.integrable_paperFT_ofReal
      (EF.integrable_fourier_of_contDiff_two hkd hkc)).re.congr (Eventually.of_forall fun τ => ?_)
    simp only [hval, RCLike.re_to_complex, Complex.ofReal_re]
  set N := ∫ t, ‖f t‖ ^ 2 with hN
  set C := 2 * a * N with hC
  have hHM := muMid_le_muHigh hR
  have hML := muLow_le_muMid
  set indR : ℝ → ℝ := (Icc (-R) R).indicator fun _ => (1 : ℝ) with hindR
  set ind4 : ℝ → ℝ := (Icc (-4) 4).indicator fun _ => (1 : ℝ) with hind4
  have hint_R : Integrable indR :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hint_4 : Integrable ind4 :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hptw : ∀ τ : ℝ, muHigh R * ‖paperFT f τ‖ ^ 2 - (muHigh R - muMid) * C * indR τ -
      (muMid - muLow) * C * ind4 τ ≤ ‖paperFT f τ‖ ^ 2 * mu τ := by
    intro τ
    have hfb : ‖paperFT f τ‖ ^ 2 ≤ C := norm_paperFT_sq_le ha hf.continuous hfs τ
    have hX : 0 ≤ ‖paperFT f τ‖ ^ 2 := sq_nonneg _
    by_cases h4 : |τ| ≤ 4
    · have hτR : τ ∈ Icc (-R) R := abs_le.mp (h4.trans hR)
      have hτ4 : τ ∈ Icc (-4 : ℝ) 4 := abs_le.mp h4
      rw [hindR, hind4, Set.indicator_of_mem hτR, Set.indicator_of_mem hτ4, mul_one, mul_one]
      have hμ := mu_ge_neg τ
      have e1 : ‖paperFT f τ‖ ^ 2 * muLow ≤ ‖paperFT f τ‖ ^ 2 * mu τ :=
        mul_le_mul_of_nonneg_left hμ hX
      have e2 : (muHigh R - muMid) * ‖paperFT f τ‖ ^ 2 ≤ (muHigh R - muMid) * C :=
        mul_le_mul_of_nonneg_left hfb (by linarith)
      have e3 : (muMid - muLow) * ‖paperFT f τ‖ ^ 2 ≤ (muMid - muLow) * C :=
        mul_le_mul_of_nonneg_left hfb (by linarith)
      nlinarith
    · push Not at h4
      have hτ4 : τ ∉ Icc (-4 : ℝ) 4 := fun h => by linarith [abs_le.mpr h]
      rw [hind4, Set.indicator_of_notMem hτ4, mul_zero, sub_zero]
      have hμ := mu_ge_log_abs h4.le
      by_cases hRτ : |τ| ≤ R
      · rw [hindR, Set.indicator_of_mem (show τ ∈ Icc (-R) R from abs_le.mp hRτ), mul_one]
        have hmid : muMid ≤ mu τ := by
          refine le_trans ?_ hμ
          rw [muMid, div_le_div_iff_of_pos_right (by positivity)]
          have h1 : Real.log 4 ≤ Real.log |τ| := Real.log_le_log (by norm_num) h4.le
          have h2 : 6 / |τ| ≤ 3 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
          linarith
        have e1 : ‖paperFT f τ‖ ^ 2 * muMid ≤ ‖paperFT f τ‖ ^ 2 * mu τ :=
          mul_le_mul_of_nonneg_left hmid hX
        have e2 : (muHigh R - muMid) * ‖paperFT f τ‖ ^ 2 ≤ (muHigh R - muMid) * C :=
          mul_le_mul_of_nonneg_left hfb (by linarith)
        nlinarith
      · push Not at hRτ
        have hτR : τ ∉ Icc (-R) R := fun h => by linarith [abs_le.mpr h]
        rw [hindR, Set.indicator_of_notMem hτR, mul_zero, sub_zero]
        have hhigh : muHigh R ≤ mu τ := by
          refine le_trans ?_ hμ
          rw [muHigh, div_le_div_iff_of_pos_right (by positivity)]
          have h1 : Real.log R ≤ Real.log |τ| := Real.log_le_log (by linarith) hRτ.le
          have h2 : 6 / |τ| ≤ 6 / R := div_le_div_of_nonneg_left (by norm_num) (by linarith)
            hRτ.le
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hhigh hX]
  have hlow : Integrable fun τ : ℝ => muHigh R * ‖paperFT f τ‖ ^ 2 -
      (muHigh R - muMid) * C * indR τ - (muMid - muLow) * C * ind4 τ :=
    ((hint_sq.const_mul _).sub (hint_R.const_mul _)).sub (hint_4.const_mul _)
  have hmono := integral_mono hlow hint_mu hptw
  have hR_val : ∫ τ, indR τ = 2 * R := by
    rw [hindR, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  have h4_val : ∫ τ, ind4 τ = 8 := by
    rw [hind4, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul, mul_one]
    norm_num
  have i1 : Integrable fun τ : ℝ => muHigh R * ‖paperFT f τ‖ ^ 2 -
      (muHigh R - muMid) * C * indR τ := (hint_sq.const_mul _).sub (hint_R.const_mul _)
  rw [integral_sub i1 (hint_4.const_mul _),
    integral_sub (hint_sq.const_mul _) (hint_R.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, hR_val, h4_val,
    integral_norm_sq_paperFT_eq hf hfs] at hmono
  refine le_trans (le_of_eq ?_) hmono
  rw [hC]
  ring

/-- `sinh a − a ≤ a²` for `0 ≤ a ≤ 1`. -/
theorem pairEnergy_half_le_sq {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : pairEnergy (1 / 2) a ≤ a ^ 2 := by
  unfold pairEnergy
  rw [show 2 * (1 / 2 : ℝ) * a = a by ring, show 2 * (1 / 2 : ℝ) = 1 by ring, div_one,
    Real.sinh_eq]
  have h1 := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := a) (by rw [abs_of_nonneg ha]; exact ha1))
  have h2 := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := -a) (by rw [abs_neg, abs_of_nonneg ha]; exact ha1))
  rw [neg_sq] at h2
  linarith [h1.2, h2.1]

/-- **Weil positivity of `ζ` below aperture `1/100`.** Every `C²` test supported in `[−a, a]`,
`0 < a ≤ 1/100`, has `Re W_ζ(f, f) ≥ ‖f‖²/25`. -/
theorem zetaZeroConfig_re_W_ge_of_aperture_le_hundredth {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 100)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    (1 / 25) * ∫ t, ‖f t‖ ^ 2 ≤ (zetaZeroConfig.W f f).re := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have ha2 : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  have hfs' : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hks : tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset hfs' hfs'
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig (EF.weilTest f f) hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (EF.weilTest f f) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  have hW : zetaZeroConfig.W f f = paperFT (EF.weilTest f f) (I / 2) +
      paperFT (EF.weilTest f f) (-I / 2) + ∫ τ : ℝ, paperFT (EF.weilTest f f) τ * (mu τ : ℂ) := by
    rw [ZeroConfig.W, ← hterm, heq, EF.literatureRHS,
      tsum_vonMangoldt_eq_zero_of_small_support ha2 hks, sub_zero, EF.gamma_term]
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest f f) τ * (mu τ : ℂ)).re =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * mu τ := by
    have h : (fun τ : ℝ => paperFT (EF.weilTest f f) τ * (mu τ : ℂ)) =
        fun τ : ℝ => ((‖paperFT f τ‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ
      rw [paperFT_weilTest_self_ofReal hf.continuous hfc τ, Complex.ofReal_mul]
    rw [h, integral_complex_ofReal, Complex.ofReal_re]
  have hpole := neg_le_re_pole_terms ha0.le hf.continuous hfs
  -- the archimedean term with `R = π/(4a)`
  set R := π / (4 * a) with hRdef
  have hR25 : 25 * π ≤ R := by
    rw [hRdef, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hR4 : 4 ≤ R := by linarith [Real.pi_gt_three]
  have harch := integral_norm_sq_paperFT_mul_mu_ge_three_band ha0.le hR4 hf hfs
  have hS := pairEnergy_half_le_sq ha0.le (by linarith)
  -- numerics
  have h4aR : 4 * a * R = π := by rw [hRdef]; field_simp
  have hlog2π : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul two_ne_zero Real.pi_ne_zero
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlogR : Real.log 25 + Real.log π ≤ Real.log R := by
    rw [← Real.log_mul (by norm_num) Real.pi_ne_zero]
    exact Real.log_le_log (by positivity) hR25
  have hlog25 : 2 + Real.log π < Real.log 25 := by
    have he : Real.exp 2 < 7.39 := by
      have h1 := Real.exp_one_lt_d9
      have h0 := Real.exp_pos 1
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have hlt : Real.exp 2 * π < 25 := by nlinarith [Real.pi_lt_d4, Real.exp_pos 2]
    have : 2 < Real.log (25 / π) :=
      (Real.lt_log_iff_exp_lt (by positivity)).mpr (by rw [lt_div_iff₀ Real.pi_pos]; exact hlt)
    rw [Real.log_div (by norm_num) Real.pi_ne_zero] at this
    linarith
  have h6R : 6 / R ≤ 6 / (25 * π) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hR25
  have h6R' : 6 / (25 * π) ≤ 0.08 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  have hlog2 := Real.log_two_lt_d9
  have hcoef : 1 / 25 ≤ 2 * π * muHigh R - 4 * a * R * (muHigh R - muMid) -
      16 * a * (muMid - muLow) - 2 * pairEnergy (1 / 2) a := by
    rw [h4aR]
    have hH : 2 * π * muHigh R - π * (muHigh R - muMid) =
        (Real.log R - Real.log (2 * π) - 6 / R + (Real.log 4 - Real.log (2 * π) - 3 / 2)) / 2 := by
      rw [muHigh, muMid]
      field_simp
      ring
    have hL : 16 * a * (muMid - muLow) = 8 * a / π * (Real.log 2 + 11 / 2) := by
      rw [muMid, muLow, hlog4, hlog2π]
      field_simp
      ring
    have hL' : 8 * a / π * (Real.log 2 + 11 / 2) ≤ 0.16 := by
      have h1 : 8 * a / π ≤ 0.08 / 3.14 := by
        rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_d2]
      have h2 : 0 ≤ Real.log 2 + 11 / 2 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      have h3 : Real.log 2 + 11 / 2 ≤ 6.2 := by norm_num at hlog2; linarith
      have h4 : 0 ≤ 8 * a / π := by positivity
      nlinarith
    have hsq : 2 * pairEnergy (1 / 2) a ≤ 0.0002 := by nlinarith
    rw [show 2 * π * muHigh R - π * (muHigh R - muMid) - 16 * a * (muMid - muLow) -
        2 * pairEnergy (1 / 2) a = (2 * π * muHigh R - π * (muHigh R - muMid)) -
          16 * a * (muMid - muLow) - 2 * pairEnergy (1 / 2) a by ring, hH, hL]
    rw [hlog4, hlog2π]
    linarith
  rw [hW, Complex.add_re, hμre]
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hcoef hN0]

/-- **Weil positivity of `ζ` on aperture `1/100`.** -/
theorem zetaZeroConfig_re_W_nonneg_of_aperture_le_hundredth {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(1 / 100)) (1 / 100)) : 0 ≤ (zetaZeroConfig.W f f).re :=
  le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (zetaZeroConfig_re_W_ge_of_aperture_le_hundredth (by norm_num) le_rfl hf hfs)

/-- **Windowed positivity for `ζ` at aperture `1/100`.** For every window supported in
`[−1/100, 1/100]` and every test of arbitrary aperture, the windowed Weil form of the zeros of
`ζ` has nonnegative real part. -/
theorem re_windowedW_zetaZeroConfig_nonneg_of_hundredth {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-(1 / 100)) (1 / 100)) :
    0 ≤ (windowedW zetaZeroConfig f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _ temperedConfig_zetaZeroConfig
    (fun _ hg hgs => zetaZeroConfig_re_W_nonneg_of_aperture_le_hundredth hg hgs) hf hfc hη hηs

end GaloisForLFunctions.SquareRootThreshold
