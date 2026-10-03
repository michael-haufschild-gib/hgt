import GaloisForLFunctions.RHTower.ZetaGateDeepLeftLine
import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform
import GaloisForLFunctions.RHTower.RouteBOfflineDomination

/-!
# Product-AFE left-line remainders on `Re w = −7/10`

The smoothed and dual diagonals of the product approximate functional equation leave the
remainders `smoothLeft` and `dualLeft`, integrals over `Re w = −1/4`.  This module moves them to
`Re w = −7/10`.

* The smoothed-diagonal integrand `ζ(2σ₀ + 2w)(x/c)^w e^{w²}/w` is holomorphic on the whole strip
  `−7/10 ≤ Re w ≤ −1/4` for `9/20 ≤ σ₀ ≤ ½`, so the full line moves and
  `‖smoothLeft‖ ≤ K (x/c)^{−7/10}`.
* The dual-diagonal integrand carries `χ(½ − d ± iτ − w)`, whose poles at `w = −½ − d ± iτ` lie
  inside the strip.  Cauchy's theorem is applied only on the rectangle `|Im w| ≤ |τ|/2`, which
  avoids them; the two horizontal edges and the unshifted tails `|Im w| > |τ|/2` are
  Gaussian-small.  On the shifted part both `χ` factors sit on `Re s = 6/5 − d`, where
  `‖χ(σ+it)‖ ≤ C(1+|t|)^{−(σ−½)}`, and so
  `‖dualLeft‖ ≤ K (cx)^{7/10} (1+|τ|)^{−(7/5 − 2d)}` for `|τ| ≥ 4`, `cx ≥ 1`.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower.ZetaGateProductAFE

noncomputable section

/-! ## `χ` to the right of `Re s = 1` -/

/-- `‖Γ(x + iy)‖` depends only on `|y|`. -/
theorem norm_Gamma_re_add_abs_im (x y : ℝ) :
    ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ = ‖Complex.Gamma ((x : ℂ) + ((|y| : ℝ) : ℂ) * I)‖ := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · have hc : (x : ℂ) + (y : ℂ) * I = (starRingEnd ℂ) ((x : ℂ) + ((|y| : ℝ) : ℂ) * I) := by
      rw [abs_of_neg hy]
      apply Complex.ext <;> simp
    rw [hc, Complex.Gamma_conj, Complex.norm_conj]

/-- `Γ_ℝ(1 − s)` has no pole for `1 < Re s < 3`. -/
theorem gammaℝ_one_sub_ne_zero_of_re {s : ℂ} (h1 : 1 < s.re) (h3 : s.re < 3) :
    Gammaℝ (1 - s) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have hre := congrArg Complex.re hn
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at hre
  norm_num at hre
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · rw [hn0] at hre
    norm_num at hre
    linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    linarith

/-- **`χ` above height two on `½ ≤ Re s ≤ 6/5`.**  `‖χ(σ+it)‖ ≤ C(1+|t|)^{−(σ−½)}` for `|t| ≥ 2`,
by Stirling through `Γ((1−s)/2) = Γ((3−s)/2)/((1−s)/2)` and the uniform vertical Gamma ratio. -/
theorem exists_norm_zetaChi_le_of_two_le_abs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 6 / 5 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (-(σ - 1 / 2)) := by
  obtain ⟨c, C', hc, hC', hratio⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio (a₁ := 3 / 5) (δ₁ := 1)
      (by norm_num) (by norm_num)
  refine ⟨3 * Real.pi / c, by positivity, fun σ t hσ1 hσ2 ht => ?_⟩
  have he0 : 0 ≤ σ - 1 / 2 := by linarith
  have he1 : σ - 1 / 2 ≤ 1 := by linarith
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set τ : ℝ := |t| / 2 with hτ
  have hτ1 : 1 ≤ τ := by rw [hτ]; linarith
  have hτ0 : 0 < τ := by linarith
  have hhalf : (1 - s) / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hs] at this
    rw [this, abs_zero] at ht
    linarith
  have hadd : (1 - s) / 2 + 1 = ((((3 - σ) / 2 : ℝ)) : ℂ) + (((-t / 2 : ℝ)) : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hden : s / 2 = (((σ / 2 : ℝ)) : ℂ) + (((t / 2 : ℝ)) : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hG1 := Complex.Gamma_add_one ((1 - s) / 2) hhalf
  rw [hadd] at hG1
  have hnum : ‖Complex.Gamma ((1 - s) / 2)‖
      = ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
          / ‖(1 - s) / 2‖ := by
    have hn0 : ‖(1 - s) / 2‖ ≠ 0 := norm_ne_zero_iff.mpr hhalf
    rw [eq_div_iff hn0, mul_comm, ← norm_mul, ← hG1, norm_Gamma_re_add_abs_im]
    congr 3
    · push_cast; ring
    · rw [hτ, abs_div, abs_neg, abs_two]
  have hden' : ‖Complex.Gamma (s / 2)‖ = ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
    rw [hden, norm_Gamma_re_add_abs_im, hτ, abs_div, abs_two]
  have hr := (hratio (σ / 2) ((3 - 2 * σ) / 2) τ (by linarith) (by linarith) (by linarith)
    (by linarith) hτ1).1
  have hGa : 0 < ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 (σ / 2))
  have hGb : 0 < ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 _)
  set Gb := ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖ with hGbdef
  set Ga := ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ with hGadef
  have hquot : Gb / Ga ≤ τ ^ ((3 - 2 * σ) / 2) / c := by
    rw [div_le_div_iff₀ hGa hc]
    rw [le_div_iff₀ hGb] at hr
    have hτpow : τ ^ (-((3 - 2 * σ) / 2)) * τ ^ ((3 - 2 * σ) / 2) = 1 := by
      rw [← Real.rpow_add hτ0]; simp
    have key : c * τ ^ (-((3 - 2 * σ) / 2)) * Gb * τ ^ ((3 - 2 * σ) / 2) = Gb * c := by
      calc c * τ ^ (-((3 - 2 * σ) / 2)) * Gb * τ ^ ((3 - 2 * σ) / 2)
          = Gb * c * (τ ^ (-((3 - 2 * σ) / 2)) * τ ^ ((3 - 2 * σ) / 2)) := by ring
        _ = Gb * c := by rw [hτpow, mul_one]
    rw [← key]
    calc c * τ ^ (-((3 - 2 * σ) / 2)) * Gb * τ ^ ((3 - 2 * σ) / 2)
        ≤ Ga * τ ^ ((3 - 2 * σ) / 2) := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = τ ^ ((3 - 2 * σ) / 2) * Ga := by ring
  have hnorm_half : τ ≤ ‖(1 - s) / 2‖ := by
    have h2 : ‖(1 - s) / 2‖ = ‖1 - s‖ / 2 := by rw [norm_div]; norm_num
    have h := Complex.abs_im_le_norm (1 - s)
    have him : (1 - s).im = -t := by simp [hs]
    rw [him, abs_neg] at h
    rw [h2, hτ]
    linarith
  rw [norm_zetaChi_eq s, hnum, hden']
  have hsre : s.re = σ := by simp [hs]
  rw [hsre]
  -- assemble
  have hπ : Real.pi ^ (σ - 1 / 2) ≤ Real.pi := by
    calc Real.pi ^ (σ - 1 / 2) ≤ Real.pi ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) he1
      _ = Real.pi := Real.rpow_one _
  have hτexp : τ ^ ((3 - 2 * σ) / 2) / τ = τ ^ (-(σ - 1 / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hτ0]
    congr 1; ring
  have hτ3 : τ ^ (-(σ - 1 / 2)) ≤ 3 * (1 + |t|) ^ (-(σ - 1 / 2)) := by
    have h1 : (1 + |t|) / 3 ≤ τ := by rw [hτ]; linarith
    have h2 : τ ^ (-(σ - 1 / 2)) ≤ ((1 + |t|) / 3) ^ (-(σ - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    rw [Real.div_rpow hpos.le (by norm_num)] at h2
    have h3 : (3 : ℝ) ^ (-(σ - 1 / 2)) ≥ 1 / 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (show -(1 : ℝ) ≤ -(σ - 1 / 2) by linarith)
      rw [Real.rpow_neg_one] at this
      linarith [show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
    have h4 : 0 ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by positivity
    calc τ ^ (-(σ - 1 / 2)) ≤ (1 + |t|) ^ (-(σ - 1 / 2)) / (3 : ℝ) ^ (-(σ - 1 / 2)) := h2
      _ ≤ (1 + |t|) ^ (-(σ - 1 / 2)) / (1 / 3) :=
          div_le_div_of_nonneg_left h4 (by norm_num) h3
      _ = 3 * (1 + |t|) ^ (-(σ - 1 / 2)) := by ring
  calc Real.pi ^ (σ - 1 / 2)
        * (‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
            / ‖(1 - s) / 2‖)
        / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖
      = Real.pi ^ (σ - 1 / 2)
          * (‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
            / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖) / ‖(1 - s) / 2‖ := by ring
    _ ≤ Real.pi * (τ ^ ((3 - 2 * σ) / 2) / c) / τ := by
        have hq0 : 0 ≤ ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
            / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by positivity
        calc Real.pi ^ (σ - 1 / 2)
              * (‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
                / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖) / ‖(1 - s) / 2‖
            ≤ Real.pi * (τ ^ ((3 - 2 * σ) / 2) / c) / ‖(1 - s) / 2‖ := by
              gcongr
          _ ≤ Real.pi * (τ ^ ((3 - 2 * σ) / 2) / c) / τ := by
              apply div_le_div_of_nonneg_left (by positivity) hτ0 hnorm_half
    _ = (Real.pi / c) * (τ ^ ((3 - 2 * σ) / 2) / τ) := by ring
    _ = (Real.pi / c) * τ ^ (-(σ - 1 / 2)) := by rw [hτexp]
    _ ≤ (Real.pi / c) * (3 * (1 + |t|) ^ (-(σ - 1 / 2))) :=
        mul_le_mul_of_nonneg_left hτ3 (by positivity)
    _ = (3 * Real.pi / c) * (1 + |t|) ^ (-(σ - 1 / 2)) := by ring

/-- **`χ` on `11/10 ≤ Re s ≤ 6/5`.**  `‖χ(σ+it)‖ ≤ C(1+|t|)^{−(σ−½)}` for every `t`: Stirling
above height two, compactness below. -/
theorem exists_norm_zetaChi_le_rightOfOne :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 11 / 10 ≤ σ → σ ≤ 6 / 5 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (-(σ - 1 / 2)) := by
  obtain ⟨CA, hCA, hA⟩ := exists_norm_zetaChi_le_of_two_le_abs
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc (11 / 10 : ℝ) (6 / 5) ×ˢ Set.Icc (-2 : ℝ) 2)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn zetaChi K := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hG : Gammaℝ (1 - ((p.1 : ℂ) + (p.2 : ℂ) * I)) ≠ 0 :=
      gammaℝ_one_sub_ne_zero_of_re (by simp; linarith [hp.1.1]) (by simp; linarith [hp.1.2])
    exact (zetaChi_analyticAt hG).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨3 * max C₀ 0 + CA, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  have h0 : 0 ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by positivity
  rcases le_or_gt 2 |t| with ht | ht
  · refine (hA σ t (by linarith) hσ2 ht).trans ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) h0
  · -- compactness
    have hmem : (σ : ℂ) + (t : ℂ) * I ∈ K :=
      ⟨(σ, t), ⟨⟨hσ1, hσ2⟩, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩, rfl⟩
    have h := hC₀ _ hmem
    have hlow : (1 : ℝ) / 3 ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by
      have h1 : (1 + |t|) ^ (-(σ - 1 / 2)) ≥ (3 : ℝ) ^ (-(σ - 1 / 2)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
      have h2 : (3 : ℝ) ^ (-(σ - 1 / 2)) ≥ (3 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith [show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
    calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := h
      _ ≤ max C₀ 0 := le_max_left _ _
      _ = (3 * max C₀ 0) * (1 / 3) := by ring
      _ ≤ (3 * max C₀ 0) * (1 + |t|) ^ (-(σ - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ (3 * max C₀ 0 + CA) * (1 + |t|) ^ (-(σ - 1 / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith

/-! ## `ζ` on `−½ ≤ Re s ≤ ¾` -/

theorem exists_norm_riemannZeta_le_wideLeftStrip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc (-(1 / 2) : ℝ) (3 / 4) ×ˢ Set.Icc (-2 : ℝ) 2)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn riemannZeta K := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hne : (p.1 : ℂ) + (p.2 : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hp.1.2]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C₀ 0 + 20 * Real.exp 2, by positivity, fun σ t hσ0 hσ1 => ?_⟩
  rcases le_or_gt 2 |t| with ht | ht
  · have h := norm_riemannZeta_le_smoothAFE_strip (σ := σ) (t := t) (by linarith) (by linarith) ht
    refine h.trans ?_
    have h4 : 4 + |t| ≤ 4 * (1 + |t|) := by linarith [abs_nonneg t]
    calc 5 * Real.exp 2 * (1 + |t|) * (4 + |t|)
        ≤ 5 * Real.exp 2 * (1 + |t|) * (4 * (1 + |t|)) := by gcongr
      _ = 20 * Real.exp 2 * (1 + |t|) ^ 2 := by ring
      _ ≤ (max C₀ 0 + 20 * Real.exp 2) * (1 + |t|) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [le_max_right C₀ 0]
  · have hmem : (σ : ℂ) + (t : ℂ) * I ∈ K :=
      ⟨(σ, t), ⟨⟨hσ0, hσ1⟩, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩, rfl⟩
    have h := hC₀ _ hmem
    have h1 : (1 : ℝ) ≤ (1 + |t|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg t])
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := h
      _ ≤ max C₀ 0 + 20 * Real.exp 2 := by linarith [le_max_left C₀ 0, Real.exp_pos 2]
      _ = (max C₀ 0 + 20 * Real.exp 2) * 1 := by ring
      _ ≤ (max C₀ 0 + 20 * Real.exp 2) * (1 + |t|) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ## The Gaussian kernel on `Re w = −7/10` -/

theorem norm_smoothAFEGaussianKernel_rect_le (t : ℝ) :
    ‖smoothAFEGaussianKernel ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ 2 * Real.exp (49 / 100) * Real.exp (-(t ^ 2)) := by
  rw [norm_smoothAFEGaussianKernel_eq_contour]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  have hnorm : (7 / 10 : ℝ) ≤ ‖(((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)
    rw [show ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I).re = -(7 / 10) by simp, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 7 / 10)] at this
    exact this
  calc Real.exp ((-(7 / 10)) ^ 2 - t ^ 2) / ‖(((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I‖
      ≤ Real.exp ((-(7 / 10)) ^ 2 - t ^ 2) / (7 / 10) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hnorm
    _ = 10 / 7 * Real.exp (49 / 100) * Real.exp (-(t ^ 2)) := by
        rw [show ((-(7 / 10) : ℝ)) ^ 2 - t ^ 2 = 49 / 100 + -(t ^ 2) by ring, Real.exp_add]
        field_simp
    _ ≤ 2 * Real.exp (49 / 100) * Real.exp (-(t ^ 2)) := by
        have : 0 ≤ Real.exp (49 / 100) * Real.exp (-(t ^ 2)) := by positivity
        nlinarith

/-! ## The smoothed diagonal on `Re w = −7/10` -/

/-- The smoothed diagonal integrand on `Re w = −7/10`, `9/20 ≤ σ₀ ≤ ½`. -/
theorem norm_smoothDiagonalIntegrand_rect_le {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2)
    (t : ℝ) :
    ‖smoothDiagonalIntegrand σ₀ c x ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (2 * C * Real.exp (49 / 100) * (x / c) ^ (-(7 / 10 : ℝ)))
          * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) := by
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  have harg : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I))
      = ((2 * σ₀ - 7 / 5 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I))‖
      ≤ C * (1 + |2 * t|) ^ 2 := by
    rw [harg]
    exact hζ (2 * σ₀ - 7 / 5) (2 * t) (by linarith) (by linarith)
  have hp : ‖((x / c : ℝ) : ℂ) ^ ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      = (x / c) ^ (-(7 / 10 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp
  have hk := norm_smoothAFEGaussianKernel_rect_le t
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (C * (1 + |2 * t|) ^ 2) * (x / c) ^ (-(7 / 10 : ℝ))
          * (2 * Real.exp (49 / 100) * Real.exp (-(t ^ 2))) := by
        rw [hp]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hz (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (2 * C * Real.exp (49 / 100) * (x / c) ^ (-(7 / 10 : ℝ)))
          * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) := by ring

theorem integrable_smoothDiagonalIntegrand_rect {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) :
    Integrable (fun t : ℝ =>
      smoothDiagonalIntegrand σ₀ c x ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)) := by
  obtain ⟨C, hC0, hζ⟩ := exists_norm_riemannZeta_le_wideLeftStrip
  have hcont := continuous_smoothDiagonalIntegrand_line (σ₀ := σ₀) hc hx (u := -(7 / 10))
    (by norm_num) (by linarith)
  refine Integrable.mono' (integrable_one_add_abs_two_mul_sq_mul_exp_neg_sq.const_mul
    (2 * C * Real.exp (49 / 100) * (x / c) ^ (-(7 / 10 : ℝ)))) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t =>
      norm_smoothDiagonalIntegrand_rect_le hc hx hσ0 hσ1 hC0 hζ t)

/-- The smoothed diagonal integrand on a horizontal edge `u ± iT`, `−7/10 ≤ u ≤ −1/4`, `T ≥ 1`. -/
theorem norm_smoothDiagonalIntegrand_horizontal_rect_le {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, |σ| ≤ 3 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {u T : ℝ} (hu1 : -(7 / 10) ≤ u) (hu2 : u ≤ -(1 / 4)) (hT : 1 ≤ T) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * max ((x / c) ^ (-(7 / 10 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1)
        * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  have harg : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      = ((2 * σ₀ + 2 * u : ℝ) : ℂ) + ((2 * (ε * T) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ C * (2 * T) ^ N := by
    rw [harg]
    have h := hζ (2 * σ₀ + 2 * u) (2 * (ε * T)) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < T)]; linarith)
    rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (by linarith : (0 : ℝ) < T)] at h
    simpa using h
  have hp : ‖((x / c : ℝ) : ℂ) ^ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ max ((x / c) ^ (-(7 / 10 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact rpow_le_max_of_mem_Icc (div_pos hx hc) hu1 hu2
  have hk := norm_smoothAFEGaussianKernel_horizontal_le (u := u) (T := T) (by linarith)
    (by linarith) hT hε
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * (2 * T) ^ N) * max ((x / c) ^ (-(7 / 10 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ)))
          * (Real.exp 1 * Real.exp (-(T ^ 2))) :=
        mul_le_mul (mul_le_mul hz hp (norm_nonneg _) (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (C * max ((x / c) ^ (-(7 / 10 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1)
          * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by ring

theorem tendsto_smoothDiagonalIntegrand_horizontal_rect {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
      smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, hC, hζ⟩ := exists_bound_norm_riemannZeta_strip 3
  set B : ℝ := C * max ((x / c) ^ (-(7 / 10 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1
    with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ => ((9 / 20) * B * 2 ^ N) * ((0 + T) ^ N * Real.exp (-(T ^ 2))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq 0 N).const_mul ((9 / 20) * B * 2 ^ N)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbound : ∀ u ∈ Set.uIoc (-(7 / 10) : ℝ) (-(1 / 4) : ℝ),
      ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ B * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    exact norm_smoothDiagonalIntegrand_horizontal_rect_le hc hx hσ0 hσ1 hC hζ hu.1.le hu.2 hT hε
  calc ‖∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
        smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ B * ((2 * T) ^ N * Real.exp (-(T ^ 2))) * |(-(1 / 4) : ℝ) - (-(7 / 10))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ((9 / 20) * B * 2 ^ N) * ((0 + T) ^ N * Real.exp (-(T ^ 2))) := by
        rw [show |(-(1 / 4) : ℝ) - (-(7 / 10))| = 9 / 20 by norm_num, mul_pow, zero_add]
        ring

theorem differentiableOn_smoothDiagonalIntegrand_rectStrip {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ1 : σ₀ ≤ 1 / 2) :
    DifferentiableOn ℂ (smoothDiagonalIntegrand σ₀ c x) (verticalStrip (-(7 / 10)) (-(1 / 4))) := by
  intro w hw
  rw [mem_verticalStrip] at hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith [hw.2]
  have hne : (((2 * σ₀ : ℝ) : ℂ) + 2 * w) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hw.2]
  apply DifferentiableAt.differentiableWithinAt
  unfold smoothDiagonalIntegrand smoothAFEGaussianKernel
  have hz : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * w)) w :=
    (differentiableAt_riemannZeta hne).comp w (by fun_prop)
  have hp : DifferentiableAt ℂ (fun w : ℂ => ((x / c : ℝ) : ℂ) ^ w) w :=
    (differentiableAt_id).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (div_pos hx hc).ne'))
  have hk : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2) / w) w :=
    ((Complex.differentiable_exp.comp (differentiable_id.pow 2)) w).div differentiableAt_id hw0
  exact (hz.mul hp).mul hk

/-- **The smoothed-diagonal remainder on `Re w = −7/10`.** -/
theorem smoothLeft_eq_rect {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hσ0 : 9 / 20 ≤ σ₀)
    (hσ1 : σ₀ ≤ 1 / 2) :
    smoothLeft σ₀ c x = (1 / (2 * Real.pi)) •
      ∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I) := by
  unfold smoothLeft
  congr 1
  have hbot := tendsto_smoothDiagonalIntegrand_horizontal_rect hc hx (by linarith) hσ1
    (ε := -1) (Or.inr rfl)
  have htop := tendsto_smoothDiagonalIntegrand_horizontal_rect hc hx (by linarith) hσ1
    (ε := 1) (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hbot htop
  exact integral_vertical_line_eq_of_horizontal_tendsto (by norm_num)
    (differentiableOn_smoothDiagonalIntegrand_rectStrip hc hx hσ1)
    (integrable_smoothDiagonalIntegrand_rect hc hx hσ0 hσ1)
    (integrable_smoothDiagonalIntegrand_left hc hx (by linarith) hσ1) hbot htop

/-- **`‖smoothLeft‖ ≤ K (x/c)^{−7/10}`**, uniformly in `σ₀ ∈ [9/20, ½]`, `c`, `x`. -/
theorem exists_norm_smoothLeft_le_rect :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ₀ c x : ℝ, 9 / 20 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖smoothLeft σ₀ c x‖ ≤ K * (x / c) ^ (-(7 / 10 : ℝ)) := by
  obtain ⟨C, hC0, hζ⟩ := exists_norm_riemannZeta_le_wideLeftStrip
  have hG0 : 0 ≤ ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2)) :=
    integral_nonneg fun t => by positivity
  refine ⟨(1 / (2 * Real.pi)) * (2 * C * Real.exp (49 / 100)
    * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))), by positivity,
    fun σ₀ c x hσ0 hσ1 hc hx => ?_⟩
  rw [smoothLeft_eq_rect hc hx hσ0 hσ1, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hbound := fun t : ℝ => norm_smoothDiagonalIntegrand_rect_le hc hx hσ0 hσ1 hC0 hζ t
  have hnorm : ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (2 * C * Real.exp (49 / 100) * (x / c) ^ (-(7 / 10 : ℝ)))
          * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2)) := by
    calc ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖smoothDiagonalIntegrand σ₀ c x ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (2 * C * Real.exp (49 / 100) * (x / c) ^ (-(7 / 10 : ℝ)))
            * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (integrable_one_add_abs_two_mul_sq_mul_exp_neg_sq.const_mul _)
            (Filter.Eventually.of_forall fun t => hbound t)
      _ = _ := by rw [integral_const_mul]
  calc (1 / (2 * Real.pi))
        * ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(7 / 10) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * ((2 * C * Real.exp (49 / 100) * (x / c) ^ (-(7 / 10 : ℝ)))
          * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-! ## The dual diagonal: analyticity off the `χ` poles -/

theorem gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
  apply h
  rw [hn]
  simp

/-- `χ(½ − d ± iτ − w)` is analytic at `w` whenever `Im w ≠ ±τ`. -/
theorem analyticAt_zetaChi_displaced_sub_of_im {d τ : ℝ} {w : ℂ} (hw : w.im ≠ τ) :
    AnalyticAt ℂ (fun w : ℂ => zetaChi (displacedLinePt d τ - w)) w := by
  have hG : Gammaℝ (1 - (displacedLinePt d τ - w)) ≠ 0 := by
    apply gammaℝ_ne_zero_of_im_ne_zero
    simp only [displacedLinePt, Complex.sub_im, Complex.one_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add]
    intro h
    exact hw (by linarith)
  have h := zetaChi_analyticAt hG
  exact h.comp ((analyticAt_const).sub analyticAt_id)

/-- `χ(½ − d ± iτ − w)` is analytic at `w` whenever `1 < ½ − d − Re w < 3`. -/
theorem analyticAt_zetaChi_displaced_sub_of_re {d τ : ℝ} {w : ℂ} (h1 : w.re < -(1 / 2) - d)
    (h3 : -(5 / 2) - d < w.re) :
    AnalyticAt ℂ (fun w : ℂ => zetaChi (displacedLinePt d τ - w)) w := by
  have hG : Gammaℝ (1 - (displacedLinePt d τ - w)) ≠ 0 := by
    apply gammaℝ_one_sub_ne_zero_of_re
    · simp only [displacedLinePt, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        mul_one]
      linarith
    · simp only [displacedLinePt, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        mul_one]
      linarith
  exact (zetaChi_analyticAt hG).comp ((analyticAt_const).sub analyticAt_id)

theorem continuous_dualDiagonalIntegrand_rectLine {d c x τ : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (hc : 0 < c) (hx : 0 < x) :
    Continuous (fun v : ℝ =>
      dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hline : ContinuousAt (fun v : ℝ => (((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I) v := by fun_prop
  set w : ℂ := (((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I with hw
  have hwre : w.re = -(7 / 10) := by simp [hw]
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hwre] at this
    simp at this
  have hc1 := analyticAt_zetaChi_displaced_sub_of_re (d := d) (τ := τ) (w := w)
    (by rw [hwre]; linarith) (by rw [hwre]; linarith)
  have hc2 := analyticAt_zetaChi_displaced_sub_of_re (d := d) (τ := -τ) (w := w)
    (by rw [hwre]; linarith) (by rw [hwre]; linarith)
  have hm := analyticAt_smoothAFEMellinIntegrand (mul_pos hc hx) hw0
  have hne : (((1 + 2 * d : ℝ) : ℂ) + 2 * w) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero, Complex.one_re] at this
    rw [hwre] at this
    linarith
  have hz : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w)) w :=
    (differentiableAt_riemannZeta hne).comp w (by fun_prop)
  have hG : ContinuousAt (dualDiagonalIntegrand d c x τ) w := by
    unfold dualDiagonalIntegrand carrierIntegrand
    exact ((hc1.continuousAt.mul hc2.continuousAt).mul hm.continuousAt).mul hz.continuousAt
  exact ContinuousAt.comp (g := dualDiagonalIntegrand d c x τ)
    (f := fun v : ℝ => (((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I) hG hline

/-! ## The dual diagonal on `Re w = −7/10` -/

/-- The dual diagonal integrand on `Re w = −7/10`, `0 < d ≤ 1/20`.  Both `χ` factors sit on
`Re s = 6/5 − d`. -/
theorem norm_dualDiagonalIntegrand_rect_le {d c x τ : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (hc : 0 < c) (hx : 0 < x) {Cχ Cζ : ℝ} (hCχ : 0 ≤ Cχ) (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 11 / 10 ≤ σ → σ ≤ 6 / 5 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ 2)
    (v : ℝ) :
    ‖dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (8 * Cχ * Cχ * Cζ * Real.exp (49 / 100)) * (c * x) ^ (7 / 10 : ℝ)
          * (1 + |τ|) ^ (-(7 / 5 - 2 * d)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  have ha0 : (0 : ℝ) ≤ 7 / 10 - d := by linarith
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hχ' : ∀ σ : ℝ, |σ| = |τ| →
      ‖zetaChi (displacedLinePt d σ - ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        ≤ Cχ * ((1 + |v|) ^ (7 / 10 - d) * (1 + |τ|) ^ (-(7 / 10 - d))) := by
    intro σ hσ
    have harg : displacedLinePt d σ - ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I)
        = ((6 / 5 - d : ℝ) : ℂ) + ((σ - v : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have h := hχ (6 / 5 - d) (σ - v) (by linarith) (by linarith)
    rw [show (6 / 5 - d - 1 / 2 : ℝ) = 7 / 10 - d by ring] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCχ)
    have htr := one_add_abs_sub_rpow_neg_le ha0 σ v
    refine htr.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hσ]
  have h1 := hχ' τ rfl
  have h2 := hχ' (-τ) (abs_neg τ)
  have hp : ‖((c * x : ℝ) : ℂ) ^ (-((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      = (c * x) ^ (7 / 10 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hc hx)]
    simp
  have hk := norm_smoothAFEGaussianKernel_rect_le v
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ Cζ * (1 + |2 * v|) ^ 2 := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))
        = ((-(2 / 5) + 2 * d : ℝ) : ℂ) + ((2 * v : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg]
    exact hζ (-(2 / 5) + 2 * d) (2 * v) (by linarith) (by linarith)
  have hva : (1 + |v|) ^ (7 / 10 - d) * (1 + |v|) ^ (7 / 10 - d) ≤ (1 + |v|) ^ 2 := by
    rw [← Real.rpow_add (by positivity)]
    calc (1 + |v|) ^ (7 / 10 - d + (7 / 10 - d)) ≤ (1 + |v|) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by linarith)
      _ = (1 + |v|) ^ 2 := by norm_cast
  have h2v : (1 + |2 * v|) ^ 2 ≤ 4 * (1 + |v|) ^ 2 := by
    have : 1 + |2 * v| ≤ 2 * (1 + |v|) := by rw [abs_mul, abs_two]; linarith
    calc (1 + |2 * v|) ^ 2 ≤ (2 * (1 + |v|)) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = 4 * (1 + |v|) ^ 2 := by ring
  have hτa : (1 + |τ|) ^ (-(7 / 10 - d)) * (1 + |τ|) ^ (-(7 / 10 - d))
      = (1 + |τ|) ^ (-(7 / 5 - 2 * d)) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  calc ‖zetaChi (displacedLinePt d τ - ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ (Cχ * ((1 + |v|) ^ (7 / 10 - d) * (1 + |τ|) ^ (-(7 / 10 - d))))
          * (Cχ * ((1 + |v|) ^ (7 / 10 - d) * (1 + |τ|) ^ (-(7 / 10 - d))))
          * ((c * x) ^ (7 / 10 : ℝ) * (2 * Real.exp (49 / 100) * Real.exp (-(v ^ 2))))
          * (Cζ * (1 + |2 * v|) ^ 2) := by
        rw [hp]
        gcongr
    _ = (Cχ * Cχ * Cζ * (2 * Real.exp (49 / 100))) * (c * x) ^ (7 / 10 : ℝ)
          * ((1 + |τ|) ^ (-(7 / 10 - d)) * (1 + |τ|) ^ (-(7 / 10 - d)))
          * (((1 + |v|) ^ (7 / 10 - d) * (1 + |v|) ^ (7 / 10 - d)) * (1 + |2 * v|) ^ 2
              * Real.exp (-(v ^ 2))) := by ring
    _ ≤ (Cχ * Cχ * Cζ * (2 * Real.exp (49 / 100))) * (c * x) ^ (7 / 10 : ℝ)
          * ((1 + |τ|) ^ (-(7 / 10 - d)) * (1 + |τ|) ^ (-(7 / 10 - d)))
          * ((1 + |v|) ^ 2 * (4 * (1 + |v|) ^ 2) * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hva h2v (by positivity) (by positivity)
    _ = (8 * Cχ * Cχ * Cζ * Real.exp (49 / 100)) * (c * x) ^ (7 / 10 : ℝ)
          * (1 + |τ|) ^ (-(7 / 5 - 2 * d)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
        rw [hτa]; ring

theorem integrable_dualDiagonalIntegrand_rect {d c x τ : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (hc : 0 < c) (hx : 0 < x) :
    Integrable (fun v : ℝ =>
      dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_rightOfOne
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_norm_riemannZeta_le_wideLeftStrip
  refine Integrable.mono' ((integrable_one_add_abs_pow_mul_exp_neg_sq 4).const_mul
    ((8 * Cχ * Cχ * Cζ * Real.exp (49 / 100)) * (c * x) ^ (7 / 10 : ℝ)
      * (1 + |τ|) ^ (-(7 / 5 - 2 * d))))
    (continuous_dualDiagonalIntegrand_rectLine hd hd20 hc hx).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  exact norm_dualDiagonalIntegrand_rect_le hd hd20 hc hx hCχ hCζ hχ hζ v

/-! ## The dual diagonal: horizontal edges and the polynomial–Gaussian budget -/

/-- The dual integrand on a horizontal edge `u ± i|τ|/2`, `−7/10 ≤ u ≤ −1/4`, `|τ| ≥ 4`.  Both `χ`
arguments have imaginary part of modulus at least `|τ|/2`, so they stay off the poles. -/
theorem norm_dualDiagonalIntegrand_horizontal_rect_le {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hcx : 1 ≤ c * x) {CA Cζ : ℝ} {N : ℕ}
    (hCA : 0 ≤ CA)
    (hA : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 6 / 5 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ CA * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, |σ| ≤ 3 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ N)
    (hτ : 4 ≤ |τ|) {u : ℝ} (hu1 : -(7 / 10) ≤ u) (hu2 : u ≤ -(1 / 4)) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
      ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ)
          * (|τ| ^ N * Real.exp (-((|τ| / 2) ^ 2))) := by
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hT2 : 2 ≤ |τ| / 2 := by linarith
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hχ' : ∀ σ : ℝ, |σ| = |τ| →
      ‖zetaChi (displacedLinePt d σ - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖ ≤ CA := by
    intro σ hσ
    have harg : displacedLinePt d σ - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)
        = ((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * (|τ| / 2) : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have him : 2 ≤ |σ - ε * (|τ| / 2)| := by
      have h1 : |σ| ≤ |σ - ε * (|τ| / 2)| + |ε * (|τ| / 2)| := by
        have := abs_add_le (σ - ε * (|τ| / 2)) (ε * (|τ| / 2))
        simpa using this
      rw [abs_mul, hεabs, one_mul, abs_of_pos (by linarith : (0 : ℝ) < |τ| / 2), hσ] at h1
      linarith
    have h := hA (1 / 2 - d - u) (σ - ε * (|τ| / 2)) (by linarith) (by linarith) him
    refine h.trans ?_
    have h1 : (1 + |σ - ε * (|τ| / 2)|) ^ (-(1 / 2 - d - u - 1 / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (σ - ε * (|τ| / 2))])
        (by linarith)
    calc CA * (1 + |σ - ε * (|τ| / 2)|) ^ (-(1 / 2 - d - u - 1 / 2)) ≤ CA * 1 :=
          mul_le_mul_of_nonneg_left h1 hCA
      _ = CA := mul_one _
  have h1 := hχ' τ rfl
  have h2 := hχ' (-τ) (abs_neg τ)
  have hp : ‖((c * x : ℝ) : ℂ) ^ (-((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
      ≤ (c * x) ^ (7 / 10 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hc hx)]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    exact Real.rpow_le_rpow_of_exponent_le hcx (by linarith)
  have hk := norm_smoothAFEGaussianKernel_horizontal_le (u := u) (T := |τ| / 2) (by linarith)
    (by linarith) (by linarith) hε
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ)
      + 2 * ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖ ≤ Cζ * |τ| ^ N := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))
        = ((1 + 2 * d + 2 * u : ℝ) : ℂ) + ((2 * (ε * (|τ| / 2)) : ℝ) : ℂ) * I := by
      push_cast; ring
    have habs : |2 * (ε * (|τ| / 2))| = |τ| := by
      rw [abs_mul, abs_mul, hεabs, abs_two, abs_of_pos (by linarith : (0 : ℝ) < |τ| / 2)]
      ring
    rw [harg]
    have h := hζ (1 + 2 * d + 2 * u) (2 * (ε * (|τ| / 2)))
      (by rw [abs_le]; constructor <;> linarith) (by rw [habs]; linarith)
    rwa [habs] at h
  calc ‖zetaChi (displacedLinePt d τ - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
      ≤ CA * CA * ((c * x) ^ (7 / 10 : ℝ) * (Real.exp 1 * Real.exp (-((|τ| / 2) ^ 2))))
          * (Cζ * |τ| ^ N) := by
        gcongr
    _ = (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ)
          * (|τ| ^ N * Real.exp (-((|τ| / 2) ^ 2))) := by ring

/-- `y^N e^{−y²/4} ≤ (N+2)! e² (1+y)^{−2}` for `y ≥ 0`. -/
theorem pow_mul_exp_neg_half_sq_le (N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ N * Real.exp (-((y / 2) ^ 2))
      ≤ ((N + 2).factorial * Real.exp 2) * (1 + y) ^ (-(2 : ℝ)) := by
  have hy1 : (0 : ℝ) < 1 + y := by linarith
  have hfact := Real.pow_div_factorial_le_exp (1 + y) hy1.le (N + 2)
  have hf0 : (0 : ℝ) < (N + 2).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf0] at hfact
  have hpow : y ^ N ≤ (1 + y) ^ N := pow_le_pow_left₀ hy (by linarith) N
  have hexp : Real.exp (1 + y) * Real.exp (-((y / 2) ^ 2)) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (y - 2)]
  rw [Real.rpow_neg hy1.le, show (1 + y) ^ (2 : ℝ) = (1 + y) ^ 2 by norm_cast]
  have hsq : 0 < (1 + y) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hsq]
  calc y ^ N * Real.exp (-((y / 2) ^ 2)) * (1 + y) ^ 2
      ≤ (1 + y) ^ N * Real.exp (-((y / 2) ^ 2)) * (1 + y) ^ 2 := by gcongr
    _ = (1 + y) ^ (N + 2) * Real.exp (-((y / 2) ^ 2)) := by ring
    _ ≤ (Real.exp (1 + y) * (N + 2).factorial) * Real.exp (-((y / 2) ^ 2)) :=
        mul_le_mul_of_nonneg_right hfact (Real.exp_pos _).le
    _ = (N + 2).factorial * (Real.exp (1 + y) * Real.exp (-((y / 2) ^ 2))) := by ring
    _ ≤ (N + 2).factorial * Real.exp 2 := mul_le_mul_of_nonneg_left hexp hf0.le

/-! ## The dual-diagonal remainder on `Re w = −7/10` -/

/-- **The rectangle step.**  On `[−7/10, −1/4] × [−|τ|/2, |τ|/2]` neither `χ` factor has a pole, so
the central part of the line `Re w = −1/4` equals the central part of `Re w = −7/10` up to the two
horizontal edges. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_left_le_rect {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hτ : 4 ≤ |τ|) :
    ‖∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
        dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (y : ℂ) * I)‖
      ≤ ‖∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
          dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (y : ℂ) * I)‖
        + ‖∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
          dualDiagonalIntegrand d c x τ ((u : ℂ) + ((|τ| / 2 : ℝ) : ℂ) * I)‖
        + ‖∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
          dualDiagonalIntegrand d c x τ ((u : ℂ) + ((-(|τ| / 2) : ℝ) : ℂ) * I)‖ := by
  have hsub : DifferentiableOn ℂ (dualDiagonalIntegrand d c x τ)
      (Set.uIcc ((((-(7 / 10) : ℝ) : ℂ)) + ((-(|τ| / 2) : ℝ) : ℂ) * I).re
          ((((-(1 / 4) : ℝ) : ℂ)) + ((|τ| / 2 : ℝ) : ℂ) * I).re
        ×ℂ Set.uIcc ((((-(7 / 10) : ℝ) : ℂ)) + ((-(|τ| / 2) : ℝ) : ℂ) * I).im
          ((((-(1 / 4) : ℝ) : ℂ)) + ((|τ| / 2 : ℝ) : ℂ) * I).im) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add,
      add_zero]
    intro p hp
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by linarith)] at hp
    obtain ⟨⟨_, hre2⟩, ⟨him1, him2⟩⟩ := hp
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hre2
      linarith
    have himabs : |p.im| ≤ |τ| / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have him1' : p.im ≠ τ := by
      intro h
      rw [h] at himabs
      linarith
    have him2' : p.im ≠ -τ := by
      intro h
      rw [h, abs_neg] at himabs
      linarith
    have hc1 := analyticAt_zetaChi_displaced_sub_of_im (d := d) him1'
    have hc2 := analyticAt_zetaChi_displaced_sub_of_im (d := d) him2'
    have hm := analyticAt_smoothAFEMellinIntegrand (mul_pos hc hx) hp0
    have hne : (((1 + 2 * d : ℝ) : ℂ) + 2 * p) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
        Complex.im_ofNat, zero_mul, sub_zero, Complex.one_re] at this
      linarith
    have hz : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w)) p :=
      (differentiableAt_riemannZeta hne).comp p (by fun_prop)
    apply DifferentiableAt.differentiableWithinAt
    unfold dualDiagonalIntegrand carrierIntegrand
    exact ((hc1.differentiableAt.mul hc2.differentiableAt).mul hm.differentiableAt).mul hz
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dualDiagonalIntegrand d c x τ) _ _ hsub
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add,
    add_zero, smul_eq_mul] at hrect
  set A := ∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
    dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (y : ℂ) * I)
  set B := ∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
    dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (y : ℂ) * I)
  set top := ∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
    dualDiagonalIntegrand d c x τ ((u : ℂ) + ((|τ| / 2 : ℝ) : ℂ) * I)
  set bot := ∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
    dualDiagonalIntegrand d c x τ ((u : ℂ) + ((-(|τ| / 2) : ℝ) : ℂ) * I)
  have hAeq : I * A = I * B + top - bot := by linear_combination hrect
  have h1 : ‖A‖ = ‖I * A‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [h1, hAeq]
  calc ‖I * B + top - bot‖ ≤ ‖I * B + top‖ + ‖bot‖ := norm_sub_le _ _
    _ ≤ ‖I * B‖ + ‖top‖ + ‖bot‖ := by gcongr; exact norm_add_le _ _
    _ = ‖B‖ + ‖top‖ + ‖bot‖ := by rw [norm_mul, Complex.norm_I, one_mul]

/-- The shifted centre:
`‖∫_{|y| ≤ |τ|/2} G(−7/10 + iy)‖ ≤ A₁ (cx)^{7/10} (1+|τ|)^{−(7/5−2d)} J₄`. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_rect_le {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hτ : 0 ≤ |τ|) {Cχ Cζ : ℝ} (hCχ : 0 ≤ Cχ)
    (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 11 / 10 ≤ σ → σ ≤ 6 / 5 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ 2) :
    ‖∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
        dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (y : ℂ) * I)‖
      ≤ (8 * Cχ * Cχ * Cζ * Real.exp (49 / 100)) * (c * x) ^ (7 / 10 : ℝ)
          * (1 + |τ|) ^ (-(7 / 5 - 2 * d)) * ∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)) := by
  have hint := integrable_dualDiagonalIntegrand_rect (τ := τ) hd hd20 hc hx
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc ‖∫ y in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
        dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (y : ℂ) * I)‖
      ≤ ∫ y in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
        ‖dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (y : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, ‖dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (y : ℂ) * I)‖ :=
        setIntegral_le_integral hint.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ∫ y : ℝ, ((8 * Cχ * Cχ * Cζ * Real.exp (49 / 100)) * (c * x) ^ (7 / 10 : ℝ)
          * (1 + |τ|) ^ (-(7 / 5 - 2 * d))) * ((1 + |y|) ^ 4 * Real.exp (-(y ^ 2))) :=
        integral_mono hint.norm ((integrable_one_add_abs_pow_mul_exp_neg_sq 4).const_mul _)
          (fun y => norm_dualDiagonalIntegrand_rect_le hd hd20 hc hx hCχ hCζ hχ hζ y)
    _ = _ := by rw [integral_const_mul]

/-- A horizontal edge:
`‖∫_{−7/10}^{−1/4} G(u ± i|τ|/2) du‖ ≤ (9/20) A₂ (cx)^{7/10} F (1+|τ|)^{−2}`. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hcx : 1 ≤ c * x) {CA Cζ : ℝ} {N : ℕ}
    (hCA : 0 ≤ CA) (hCζ : 0 ≤ Cζ)
    (hA : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 6 / 5 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ CA * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, |σ| ≤ 3 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ N)
    (hτ : 4 ≤ |τ|) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ‖∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
        dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
      ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ)
          * (((N + 2).factorial * Real.exp 2) * (1 + |τ|) ^ (-(2 : ℝ))) * (9 / 20) := by
  have hbound : ∀ u ∈ Set.uIoc (-(7 / 10) : ℝ) (-(1 / 4)),
      ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
        ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ)
          * (((N + 2).factorial * Real.exp 2) * (1 + |τ|) ^ (-(2 : ℝ))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    refine (norm_dualDiagonalIntegrand_horizontal_rect_le hd hd20 hc hx hcx hCA hA hζ hτ
      hu.1.le hu.2 hε).trans ?_
    have hpg := pow_mul_exp_neg_half_sq_le N (abs_nonneg τ)
    have h0 : 0 ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hpg h0
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans (le_of_eq ?_)
  rw [show |(-(1 / 4) : ℝ) - (-(7 / 10))| = 9 / 20 by norm_num]

/-- The unshifted tails `|Im w| > |τ|/2` of the line `Re w = −1/4`. -/
theorem norm_setIntegral_compl_dualDiagonalIntegrand_left_le {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hτ : 4 ≤ |τ|) {Cχ Cζ : ℝ} (hCχ : 0 ≤ Cχ)
    (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ 2) :
    ‖∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (4 / |τ| ^ 2)
          * ∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)) := by
  have hgint := integrable_dualDiagonalIntegrand_left (τ := τ) hd (by linarith) hc hx
  have hM : Integrable (fun v : ℝ => ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16))
      * (c * x) ^ (1 / 4 : ℝ) * (4 / |τ| ^ 2)) * ((1 + |v|) ^ 5 * Real.exp (-(v ^ 2)))) :=
    (integrable_one_add_abs_pow_mul_exp_neg_sq 5).const_mul _
  have hpt : ∀ v ∈ (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
      ‖dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
        ≤ ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (4 / |τ| ^ 2))
          * ((1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) := by
    intro v hv
    have hv' : |τ| / 2 ≤ |v| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with hv | hv
      · rw [abs_of_neg (show v < 0 by linarith)]; linarith
      · rw [abs_of_pos (show 0 < v by linarith)]; linarith
    have hb := norm_dualDiagonalIntegrand_left_le (τ := τ) hd (by linarith) hc hx hCχ hCζ hχ hζ v
    refine hb.trans ?_
    have hτd : (1 + |τ|) ^ (-(1 / 2 - 2 * d)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by linarith)
    have hpoly : (1 + |v|) ^ 3 ≤ (4 / |τ| ^ 2) * (1 + |v|) ^ 5 := by
      have hτ2 : 0 < |τ| ^ 2 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hτ2]
      have hsq : |τ| ^ 2 ≤ 4 * (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v]
      have h3 : 0 ≤ (1 + |v|) ^ 3 := by positivity
      calc (1 + |v|) ^ 3 * |τ| ^ 2 ≤ (1 + |v|) ^ 3 * (4 * (1 + |v|) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq h3
        _ = 4 * (1 + |v|) ^ 5 := by ring
    have hK : 0 ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) := by
      positivity
    have he : 0 ≤ Real.exp (-(v ^ 2)) := (Real.exp_pos _).le
    have h3 : 0 ≤ (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) := by positivity
    calc (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
          * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2)))
        ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * 1
            * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτd hK) h3
      _ ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * 1
            * ((4 / |τ| ^ 2) * (1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hpoly he
      _ = ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (4 / |τ| ^ 2))
            * ((1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) := by ring
  calc ‖∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        ‖dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (4 / |τ| ^ 2))
          * ((1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) :=
        setIntegral_mono_on hgint.norm.integrableOn hM.integrableOn measurableSet_Ioc.compl hpt
    _ ≤ ∫ v : ℝ, ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
          * (4 / |τ| ^ 2)) * ((1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) :=
        setIntegral_le_integral hM (Filter.Eventually.of_forall fun v => by positivity)
    _ = _ := by rw [integral_const_mul]

/-- **`‖dualLeft‖ ≤ K (cx)^{7/10} (1+|τ|)^{−(7/5−2d)}`** for `0 < d ≤ 1/20`, `cx ≥ 1`, `|τ| ≥ 4`:
the rectangle step, the shifted centre, the two edges and the unshifted tails. -/
theorem exists_norm_dualLeft_le_rect :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 1 ≤ c * x →
      4 ≤ |τ| →
        ‖dualLeft d c x τ‖ ≤ K * (c * x) ^ (7 / 10 : ℝ) * (1 + |τ|) ^ (-(7 / 5 - 2 * d)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_rightOfOne
  obtain ⟨CA, hCA, hA⟩ := exists_norm_zetaChi_le_of_two_le_abs
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_norm_riemannZeta_le_wideLeftStrip
  obtain ⟨Cζ3, N, hCζ3, hζ3⟩ := exists_bound_norm_riemannZeta_strip 3
  obtain ⟨Cχl, hCχl, hχl⟩ := exists_norm_zetaChi_le_rightStrip
  obtain ⟨Cζl, hCζl, hζl⟩ := exists_norm_riemannZeta_le_leftStrip
  have hJ4 : 0 ≤ ∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)) :=
    integral_nonneg fun v => by positivity
  have hJ5 : 0 ≤ ∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)) :=
    integral_nonneg fun v => by positivity
  refine ⟨(1 / (2 * Real.pi)) * ((8 * Cχ * Cχ * Cζ * Real.exp (49 / 100))
      * (∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))
    + (9 / 10) * (CA * CA * Cζ3 * Real.exp 1) * ((N + 2).factorial * Real.exp 2)
    + (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * (25 / 4)
      * (∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)))), by positivity,
    fun d c x τ hd hd20 hc hx hcx hτ => ?_⟩
  have hE2 : (1 + |τ|) ^ (-(2 : ℝ)) ≤ (1 + |τ|) ^ (-(7 / 5 - 2 * d)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by linarith)
  have hP14 : (c * x) ^ (1 / 4 : ℝ) ≤ (c * x) ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hcx (by norm_num)
  have hτsq : 4 / |τ| ^ 2 ≤ (25 / 4) * (1 + |τ|) ^ (-(7 / 5 - 2 * d)) := by
    have h1 : 4 / |τ| ^ 2 ≤ (25 / 4) * (1 + |τ|) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), show (1 + |τ|) ^ (2 : ℝ) = (1 + |τ|) ^ 2 by norm_cast,
        ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [abs_nonneg τ]
    exact h1.trans (mul_le_mul_of_nonneg_left hE2 (by norm_num))
  -- the four pieces
  have hrect := norm_intervalIntegral_dualDiagonalIntegrand_left_le_rect (τ := τ) hd hd20 hc hx hτ
  have hcen := norm_intervalIntegral_dualDiagonalIntegrand_rect_le (τ := τ) hd hd20 hc hx
    (abs_nonneg τ) hCχ hCζ hχ hζ
  have htop := norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le (τ := τ) hd hd20 hc
    hx hcx hCA hCζ3 hA hζ3 hτ (ε := 1) (Or.inl rfl)
  have hbot := norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le (τ := τ) hd hd20 hc
    hx hcx hCA hCζ3 hA hζ3 hτ (ε := -1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at htop hbot
  have htail := norm_setIntegral_compl_dualDiagonalIntegrand_left_le (τ := τ) hd hd20 hc hx hτ
    hCχl hCζl hχl hζl
  -- split the line `Re w = −1/4` into the centre and the tails
  have hgint := integrable_dualDiagonalIntegrand_left (τ := τ) hd (by linarith) hc hx
  have hsplit := integral_add_compl (measurableSet_Ioc (a := -(|τ| / 2)) (b := |τ| / 2)) hgint
  have hcentre : ∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
      dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (y : ℂ) * I)
      = ∫ v in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
          dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I) :=
    intervalIntegral.integral_of_le (by linarith)
  rw [hcentre] at hrect
  have hdual : dualLeft d c x τ = (1 / (2 * Real.pi)) • ∫ v : ℝ,
      dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I) := rfl
  rw [hdual, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), ← hsplit]
  set E := (1 + |τ|) ^ (-(7 / 5 - 2 * d))
  set P := (c * x) ^ (7 / 10 : ℝ)
  have hE0 : 0 ≤ E := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hpieces :
      ‖(∫ v in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
          dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))
        + ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
          dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ ((8 * Cχ * Cχ * Cζ * Real.exp (49 / 100))
            * (∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))
          + (9 / 10) * (CA * CA * Cζ3 * Real.exp 1) * ((N + 2).factorial * Real.exp 2)
          + (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * (25 / 4)
            * (∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)))) * P * E := by
    refine (norm_add_le _ _).trans ?_
    have hA2 : 0 ≤ CA * CA * Cζ3 * Real.exp 1 * P * ((N + 2).factorial * Real.exp 2) := by
      positivity
    have hA3 : 0 ≤ (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) := by positivity
    have hedge : (CA * CA * Cζ3 * Real.exp 1) * P
        * (((N + 2).factorial * Real.exp 2) * (1 + |τ|) ^ (-(2 : ℝ))) * (9 / 20)
        ≤ (CA * CA * Cζ3 * Real.exp 1) * P * ((N + 2).factorial * Real.exp 2) * E * (9 / 20) := by
      have := mul_le_mul_of_nonneg_left hE2 hA2
      nlinarith
    have htail' : (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
        * (4 / |τ| ^ 2) * ∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2))
        ≤ (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * P * ((25 / 4) * E)
          * ∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)) := by
      gcongr
    refine (add_le_add (hrect.trans (add_le_add (add_le_add hcen htop) hbot)) htail).trans ?_
    refine (add_le_add (add_le_add (add_le_add le_rfl hedge) hedge) htail').trans (le_of_eq ?_)
    ring
  calc (1 / (2 * Real.pi))
        * ‖(∫ v in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
            dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))
          + ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
            dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (((8 * Cχ * Cχ * Cζ * Real.exp (49 / 100))
            * (∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))
          + (9 / 10) * (CA * CA * Cζ3 * Real.exp 1) * ((N + 2).factorial * Real.exp 2)
          + (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * (25 / 4)
            * (∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)))) * P * E) :=
        mul_le_mul_of_nonneg_left hpieces (by positivity)
    _ = _ := by ring

end

end RHTower.ZetaGateProductAFE
