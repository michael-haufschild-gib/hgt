import GaloisForLFunctions.RHTower.ZetaGateProductAFEBlockBound
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# The left-line remainders of the product approximate functional equation on `Re w = −9/20`

The smoothed diagonal `Σ_j (j+1)^{-2σ₀} V((j+1)²c/x)` and the dual diagonal of the product
approximate functional equation leave, after their two residues, the remainders `smoothLeft` and
`dualLeft`: integrals over the line `Re w = −1/4` of

* `ζ(2σ₀ + 2w)(x/c)^w e^{w²}/w`, and
* `χ(½ − d + iτ − w) χ(½ − d − iτ − w) (cx)^{−w} e^{w²}/w · ζ(1 + 2d + 2w)`.

For `σ₀ = ½ − d`, `0 < d ≤ 1/20`, both integrands are holomorphic on the strip
`−9/20 ≤ Re w ≤ −1/4`: the kernel pole is at `w = 0`, the zeta poles at `w = d` and `w = −d`, and the
poles of `χ(½ − d ± iτ − w)` have `Re w = −½ − d < −9/20`.  The Gaussian `e^{w²}` kills the horizontal
edges, so the remainders equal the integrals over `Re w = −9/20`, where

* `‖smoothLeft‖ ≤ K₁ (x/c)^{−9/20}` (`exists_norm_smoothLeft_le_deep`), using `ζ` on
  `0 ≤ σ ≤ ¾`;
* `‖dualLeft‖ ≤ K₂ (cx)^{9/20} (1 + |τ|)^{−(9/10 − 2d)}` (`exists_norm_dualLeft_le_deep`), using
  `‖χ(σ + it)‖ ≤ C (1 + |t|)^{−(σ − ½)}` on `½ ≤ σ ≤ 19/20` (`exists_norm_zetaChi_le_rightStrip_deep`).

Compared with the line `Re w = −1/4` both remainders gain the factor `(c/x)^{1/5}` at heights
`τ ≍ x`.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Filter Topology Set
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## Decay of `χ` on `½ ≤ σ ≤ 19/20` -/

theorem exists_norm_zetaChi_le_rightStrip_deep :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 19 / 20 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (-(σ - 1 / 2)) := by
  -- the compact part
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc (1 / 2 : ℝ) (19 / 20) ×ˢ Set.Icc (-256 : ℝ) 256)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn zetaChi K := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hG : Gammaℝ (1 - ((p.1 : ℂ) + (p.2 : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp
      linarith [hp.1.2]
    exact (zetaChi_analyticAt hG).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  set A : ℝ := Real.exp ((9 / 20) * (Real.log Real.pi + Real.log 2 + 2)) with hAdef
  refine ⟨max C₀ 0 * 257 + 2 * A, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have ha0 : 0 ≤ σ - 1 / 2 := by linarith
  have ha1 : σ - 1 / 2 ≤ 9 / 20 := by linarith
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  rcases le_or_gt 256 |t| with ht | ht
  · have hσ' : σ < 1 := by linarith
    have h := norm_zetaChi_le_right_line_rpow hσ1 hσ' ht
    rw [norm_zetaChi_real_add_im_eq_abs]
    refine h.trans ?_
    have hlog : 0 ≤ Real.log Real.pi + Real.log 2 + 2 := by
      have := Real.log_nonneg (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    have hexp : Real.exp ((σ - 1 / 2) * (Real.log Real.pi + Real.log 2 + 2)) ≤ A := by
      rw [hAdef]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right ha1 hlog
    have hrpow : |t| ^ (-(σ - 1 / 2)) ≤ 2 * (1 + |t|) ^ (-(σ - 1 / 2)) := by
      have h2 : 1 + |t| ≤ 2 * |t| := by linarith
      have h3 : (2 * |t|) ^ (-(σ - 1 / 2)) ≤ (1 + |t|) ^ (-(σ - 1 / 2)) :=
        Real.rpow_le_rpow_of_nonpos hpos h2 (by linarith)
      rw [Real.mul_rpow (by norm_num) (abs_nonneg t)] at h3
      have h4 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(σ - 1 / 2)) := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : -(1 : ℝ) ≤ -(σ - 1 / 2))
        rw [Real.rpow_neg_one] at this
        linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      have h6 : 0 ≤ |t| ^ (-(σ - 1 / 2)) := by positivity
      nlinarith
    calc Real.exp ((σ - 1 / 2) * (Real.log Real.pi + Real.log 2 + 2)) * |t| ^ (-(σ - 1 / 2))
        ≤ A * |t| ^ (-(σ - 1 / 2)) := mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ A * (2 * (1 + |t|) ^ (-(σ - 1 / 2))) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ ≤ (max C₀ 0 * 257 + 2 * A) * (1 + |t|) ^ (-(σ - 1 / 2)) := by
          have : 0 ≤ max C₀ 0 * 257 := by positivity
          nlinarith [(by positivity : (0 : ℝ) ≤ (1 + |t|) ^ (-(σ - 1 / 2)))]
  · have hmem : (σ : ℂ) + (t : ℂ) * I ∈ K :=
      ⟨(σ, t), ⟨⟨hσ1, hσ2⟩, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩, rfl⟩
    have h := hC₀ _ hmem
    have hlow : (1 : ℝ) / 257 ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by
      have h1 : (1 + |t|) ^ (-(σ - 1 / 2)) ≥ (257 : ℝ) ^ (-(σ - 1 / 2)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
      have h2 : (257 : ℝ) ^ (-(σ - 1 / 2)) ≥ (257 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith [show (257 : ℝ)⁻¹ = 1 / 257 by norm_num]
    calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := h
      _ ≤ max C₀ 0 := le_max_left _ _
      _ = (max C₀ 0 * 257) * (1 / 257) := by ring
      _ ≤ (max C₀ 0 * 257) * (1 + |t|) ^ (-(σ - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ (max C₀ 0 * 257 + 2 * A) * (1 + |t|) ^ (-(σ - 1 / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [(by positivity : (0 : ℝ) ≤ A)]

/-! ## Powers on a vertical strip -/

theorem rpow_le_max_of_mem_Icc {b u lo hi : ℝ} (hb : 0 < b) (hlo : lo ≤ u) (hhi : u ≤ hi) :
    b ^ u ≤ max (b ^ lo) (b ^ hi) := by
  rcases le_or_gt 1 b with hb1 | hb1
  · exact (Real.rpow_le_rpow_of_exponent_le hb1 hhi).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hb hb1.le hlo).trans (le_max_left _ _)

/-- The Gaussian kernel on a horizontal edge `u ± iT`, `|u| ≤ 1`, `T ≥ 1`. -/
theorem norm_smoothAFEGaussianKernel_horizontal_le {u T ε : ℝ} (hu1 : -1 ≤ u) (hu2 : u ≤ 1)
    (hT : 1 ≤ T) (hε : ε = 1 ∨ ε = -1) :
    ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ Real.exp 1 * Real.exp (-(T ^ 2)) := by
  have hεsq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  rw [norm_smoothAFEGaussianKernel_eq_contour]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  have hnorm : T ≤ ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
    rw [abs_mul, hεabs, one_mul, abs_of_pos (by linarith : (0 : ℝ) < T)] at this
    exact this
  have hu2' : u ^ 2 ≤ 1 := by nlinarith
  have hsq : (ε * T) ^ 2 = T ^ 2 := by rw [mul_pow, hεsq, one_mul]
  rw [hsq]
  calc Real.exp (u ^ 2 - T ^ 2) / ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖
      ≤ Real.exp (u ^ 2 - T ^ 2) / 1 := by
        apply div_le_div_of_nonneg_left (Real.exp_pos _).le one_pos
        linarith
    _ = Real.exp (u ^ 2) * Real.exp (-(T ^ 2)) := by rw [div_one, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp 1 * Real.exp (-(T ^ 2)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu2') (Real.exp_pos _).le

/-- The Gaussian kernel on the line `Re w = −9/20`. -/
theorem norm_smoothAFEGaussianKernel_deep_le (t : ℝ) :
    ‖smoothAFEGaussianKernel ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ 3 * Real.exp (81 / 400) * Real.exp (-(t ^ 2)) := by
  rw [norm_smoothAFEGaussianKernel_eq_contour]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  have hnorm : (9 / 20 : ℝ) ≤ ‖(((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)
    rw [show ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I).re = -(9 / 20) by simp, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 9 / 20)] at this
    exact this
  calc Real.exp ((-(9 / 20)) ^ 2 - t ^ 2) / ‖(((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I‖
      ≤ Real.exp ((-(9 / 20)) ^ 2 - t ^ 2) / (9 / 20) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hnorm
    _ = 20 / 9 * Real.exp (81 / 400) * Real.exp (-(t ^ 2)) := by
        rw [show ((-(9 / 20) : ℝ)) ^ 2 - t ^ 2 = 81 / 400 + -(t ^ 2) by ring, Real.exp_add]
        field_simp
    _ ≤ 3 * Real.exp (81 / 400) * Real.exp (-(t ^ 2)) := by
        have : 0 ≤ Real.exp (81 / 400) * Real.exp (-(t ^ 2)) := by positivity
        nlinarith

/-! ## The smoothed diagonal on the deep line -/

/-- The smoothed diagonal integrand on `Re w = −9/20`, `9/20 ≤ σ₀ ≤ ½`. -/
theorem norm_smoothDiagonalIntegrand_deep_le {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 3 / 4 → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2)
    (t : ℝ) :
    ‖smoothDiagonalIntegrand σ₀ c x ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (3 * C * Real.exp (81 / 400) * (x / c) ^ (-(9 / 20 : ℝ)))
          * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) := by
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  have harg : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I))
      = ((2 * σ₀ - 9 / 10 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I))‖
      ≤ C * (1 + |2 * t|) ^ 2 := by
    rw [harg]
    exact hζ (2 * σ₀ - 9 / 10) (2 * t) (by linarith) (by linarith)
  have hp : ‖((x / c : ℝ) : ℂ) ^ ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      = (x / c) ^ (-(9 / 20 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp
  have hk := norm_smoothAFEGaussianKernel_deep_le t
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (C * (1 + |2 * t|) ^ 2) * (x / c) ^ (-(9 / 20 : ℝ))
          * (3 * Real.exp (81 / 400) * Real.exp (-(t ^ 2))) := by
        rw [hp]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hz (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (3 * C * Real.exp (81 / 400) * (x / c) ^ (-(9 / 20 : ℝ)))
          * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) := by ring

theorem integrable_smoothDiagonalIntegrand_deep {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) :
    Integrable (fun t : ℝ =>
      smoothDiagonalIntegrand σ₀ c x ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)) := by
  obtain ⟨C, hC0, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hcont := continuous_smoothDiagonalIntegrand_line (σ₀ := σ₀) hc hx (u := -(9 / 20))
    (by norm_num) (by linarith)
  refine Integrable.mono' (integrable_one_add_abs_two_mul_sq_mul_exp_neg_sq.const_mul
    (3 * C * Real.exp (81 / 400) * (x / c) ^ (-(9 / 20 : ℝ)))) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_smoothDiagonalIntegrand_deep_le hc hx hσ0 hσ1 hC0 hζ t)

/-- The smoothed diagonal integrand on a horizontal edge `u ± iT`, `−9/20 ≤ u ≤ −1/4`, `T ≥ 1`. -/
theorem norm_smoothDiagonalIntegrand_horizontal_deep_le {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, |σ| ≤ 3 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {u T : ℝ} (hu1 : -(9 / 20) ≤ u) (hu2 : u ≤ -(1 / 4)) (hT : 1 ≤ T) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * max ((x / c) ^ (-(9 / 20 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1)
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
      ≤ max ((x / c) ^ (-(9 / 20 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact rpow_le_max_of_mem_Icc (div_pos hx hc) hu1 hu2
  have hk := norm_smoothAFEGaussianKernel_horizontal_le (u := u) (T := T) (by linarith) (by linarith) hT hε
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * (2 * T) ^ N) * max ((x / c) ^ (-(9 / 20 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ)))
          * (Real.exp 1 * Real.exp (-(T ^ 2))) :=
        mul_le_mul (mul_le_mul hz hp (norm_nonneg _) (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (C * max ((x / c) ^ (-(9 / 20 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1)
          * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by ring

theorem tendsto_smoothDiagonalIntegrand_horizontal_deep {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-(9 / 20) : ℝ)..(-(1 / 4) : ℝ),
      smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, hC, hζ⟩ := exists_bound_norm_riemannZeta_strip 3
  set B : ℝ := C * max ((x / c) ^ (-(9 / 20 : ℝ))) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1
    with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ => ((1 / 5) * B * 2 ^ N) * ((0 + T) ^ N * Real.exp (-(T ^ 2))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq 0 N).const_mul ((1 / 5) * B * 2 ^ N)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbound : ∀ u ∈ Set.uIoc (-(9 / 20) : ℝ) (-(1 / 4) : ℝ),
      ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ B * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    exact norm_smoothDiagonalIntegrand_horizontal_deep_le hc hx hσ0 hσ1 hC hζ hu.1.le hu.2 hT hε
  calc ‖∫ u : ℝ in (-(9 / 20) : ℝ)..(-(1 / 4) : ℝ),
        smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ B * ((2 * T) ^ N * Real.exp (-(T ^ 2))) * |(-(1 / 4) : ℝ) - (-(9 / 20))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ((1 / 5) * B * 2 ^ N) * ((0 + T) ^ N * Real.exp (-(T ^ 2))) := by
        rw [show |(-(1 / 4) : ℝ) - (-(9 / 20))| = 1 / 5 by norm_num, mul_pow, zero_add]
        ring

theorem differentiableOn_smoothDiagonalIntegrand_deepStrip {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ1 : σ₀ ≤ 1 / 2) :
    DifferentiableOn ℂ (smoothDiagonalIntegrand σ₀ c x) (verticalStrip (-(9 / 20)) (-(1 / 4))) := by
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

/-- **The smoothed-diagonal remainder on the deep line.** -/
theorem smoothLeft_eq_deep {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hσ0 : 9 / 20 ≤ σ₀)
    (hσ1 : σ₀ ≤ 1 / 2) :
    smoothLeft σ₀ c x = (1 / (2 * Real.pi)) •
      ∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I) := by
  unfold smoothLeft
  congr 1
  have hbot := tendsto_smoothDiagonalIntegrand_horizontal_deep hc hx (by linarith) hσ1
    (ε := -1) (Or.inr rfl)
  have htop := tendsto_smoothDiagonalIntegrand_horizontal_deep hc hx (by linarith) hσ1
    (ε := 1) (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hbot htop
  exact integral_vertical_line_eq_of_horizontal_tendsto (by norm_num)
    (differentiableOn_smoothDiagonalIntegrand_deepStrip hc hx hσ1)
    (integrable_smoothDiagonalIntegrand_deep hc hx hσ0 hσ1)
    (integrable_smoothDiagonalIntegrand_left hc hx (by linarith) hσ1) hbot htop

/-- **`‖smoothLeft‖ ≤ K₁ (x/c)^{−9/20}`**, uniformly in `σ₀ ∈ [9/20, ½]`, `c`, `x`. -/
theorem exists_norm_smoothLeft_le_deep :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ₀ c x : ℝ, 9 / 20 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖smoothLeft σ₀ c x‖ ≤ K * (x / c) ^ (-(9 / 20 : ℝ)) := by
  obtain ⟨C, hC0, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hG0 : 0 ≤ ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2)) :=
    integral_nonneg fun t => by positivity
  refine ⟨(1 / (2 * Real.pi)) * (3 * C * Real.exp (81 / 400)
    * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))), by positivity,
    fun σ₀ c x hσ0 hσ1 hc hx => ?_⟩
  rw [smoothLeft_eq_deep hc hx hσ0 hσ1, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hbound := fun t : ℝ => norm_smoothDiagonalIntegrand_deep_le hc hx hσ0 hσ1 hC0 hζ t
  have hnorm : ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (3 * C * Real.exp (81 / 400) * (x / c) ^ (-(9 / 20 : ℝ)))
          * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2)) := by
    calc ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖smoothDiagonalIntegrand σ₀ c x ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (3 * C * Real.exp (81 / 400) * (x / c) ^ (-(9 / 20 : ℝ)))
            * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (integrable_one_add_abs_two_mul_sq_mul_exp_neg_sq.const_mul _)
            (Filter.Eventually.of_forall fun t => hbound t)
      _ = _ := by rw [integral_const_mul]
  calc (1 / (2 * Real.pi))
        * ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-(9 / 20) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * ((3 * C * Real.exp (81 / 400) * (x / c) ^ (-(9 / 20 : ℝ)))
          * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-! ## The dual diagonal on the deep line -/

/-- The dual diagonal integrand on `Re w = −9/20`, `0 < d ≤ 1/20`. -/
theorem norm_dualDiagonalIntegrand_deep_le {d c x τ : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (hc : 0 < c) (hx : 0 < x) {Cχ Cζ : ℝ} (hCχ : 0 ≤ Cχ) (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 19 / 20 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 3 / 4 → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ 2)
    (v : ℝ) :
    ‖dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (12 * Cχ * Cχ * Cζ * Real.exp (81 / 400)) * (c * x) ^ (9 / 20 : ℝ)
          * (1 + |τ|) ^ (-(9 / 10 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
  have ha0 : (0 : ℝ) ≤ 9 / 20 - d := by linarith
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hχ' : ∀ σ : ℝ, |σ| = |τ| →
      ‖zetaChi (displacedLinePt d σ - ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        ≤ Cχ * ((1 + |v|) ^ (9 / 20 - d) * (1 + |τ|) ^ (-(9 / 20 - d))) := by
    intro σ hσ
    have harg : displacedLinePt d σ - ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)
        = ((19 / 20 - d : ℝ) : ℂ) + ((σ - v : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have h := hχ (19 / 20 - d) (σ - v) (by linarith) (by linarith)
    rw [show (19 / 20 - d - 1 / 2 : ℝ) = 9 / 20 - d by ring] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCχ)
    have htr := one_add_abs_sub_rpow_neg_le ha0 σ v
    refine htr.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h1 := hχ' τ rfl
  have h2 := hχ' (-τ) (abs_neg τ)
  have hp : ‖((c * x : ℝ) : ℂ) ^ (-((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      = (c * x) ^ (9 / 20 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hc hx)]
    simp
  have hk := norm_smoothAFEGaussianKernel_deep_le v
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ Cζ * (1 + |2 * v|) ^ 2 := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))
        = ((1 / 10 + 2 * d : ℝ) : ℂ) + ((2 * v : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg]
    exact hζ (1 / 10 + 2 * d) (2 * v) (by linarith) (by linarith)
  have hva : (1 + |v|) ^ (9 / 20 - d) * (1 + |v|) ^ (9 / 20 - d) ≤ 1 + |v| := by
    rw [← Real.rpow_add (by positivity)]
    calc (1 + |v|) ^ (9 / 20 - d + (9 / 20 - d)) ≤ (1 + |v|) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by linarith)
      _ = 1 + |v| := Real.rpow_one _
  have h2v : (1 + |2 * v|) ^ 2 ≤ 4 * (1 + |v|) ^ 2 := by
    have : 1 + |2 * v| ≤ 2 * (1 + |v|) := by rw [abs_mul, abs_two]; linarith
    calc (1 + |2 * v|) ^ 2 ≤ (2 * (1 + |v|)) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = 4 * (1 + |v|) ^ 2 := by ring
  have hτa : (1 + |τ|) ^ (-(9 / 20 - d)) * (1 + |τ|) ^ (-(9 / 20 - d))
      = (1 + |τ|) ^ (-(9 / 10 - 2 * d)) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  calc ‖zetaChi (displacedLinePt d τ - ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ (Cχ * ((1 + |v|) ^ (9 / 20 - d) * (1 + |τ|) ^ (-(9 / 20 - d))))
          * (Cχ * ((1 + |v|) ^ (9 / 20 - d) * (1 + |τ|) ^ (-(9 / 20 - d))))
          * ((c * x) ^ (9 / 20 : ℝ) * (3 * Real.exp (81 / 400) * Real.exp (-(v ^ 2))))
          * (Cζ * (1 + |2 * v|) ^ 2) := by
        rw [hp]
        gcongr
    _ = (Cχ * Cχ * Cζ * (3 * Real.exp (81 / 400))) * (c * x) ^ (9 / 20 : ℝ)
          * ((1 + |τ|) ^ (-(9 / 20 - d)) * (1 + |τ|) ^ (-(9 / 20 - d)))
          * (((1 + |v|) ^ (9 / 20 - d) * (1 + |v|) ^ (9 / 20 - d)) * (1 + |2 * v|) ^ 2
              * Real.exp (-(v ^ 2))) := by ring
    _ ≤ (Cχ * Cχ * Cζ * (3 * Real.exp (81 / 400))) * (c * x) ^ (9 / 20 : ℝ)
          * ((1 + |τ|) ^ (-(9 / 20 - d)) * (1 + |τ|) ^ (-(9 / 20 - d)))
          * ((1 + |v|) * (4 * (1 + |v|) ^ 2) * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hva h2v (by positivity) (by positivity)
    _ = (12 * Cχ * Cχ * Cζ * Real.exp (81 / 400)) * (c * x) ^ (9 / 20 : ℝ)
          * (1 + |τ|) ^ (-(9 / 10 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
        rw [hτa]; ring

theorem integrable_dualDiagonalIntegrand_deep {d c x τ : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (hc : 0 < c) (hx : 0 < x) :
    Integrable (fun v : ℝ =>
      dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_rightStrip_deep
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hcont := continuous_dualDiagonalIntegrand_line (d := d) (τ := τ) hc hx (u := -(9 / 20))
    (by norm_num) (by linarith) (by linarith)
  refine Integrable.mono' (integrable_one_add_abs_cube_mul_exp_neg_sq.const_mul
    ((12 * Cχ * Cχ * Cζ * Real.exp (81 / 400)) * (c * x) ^ (9 / 20 : ℝ)
      * (1 + |τ|) ^ (-(9 / 10 - 2 * d))))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  exact norm_dualDiagonalIntegrand_deep_le hd hd20 hc hx hCχ hCζ hχ hζ v

/-- The dual integrand on a horizontal edge `u ± iT`, `−9/20 ≤ u ≤ −1/4`. -/
theorem norm_dualDiagonalIntegrand_horizontal_deep_le {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) {Cχ Cζ : ℝ} {Nχ Nζ : ℕ} {T₀ : ℝ}
    (hCχ : 0 ≤ Cχ) (hCζ : 0 ≤ Cζ)
    (hχ : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 1 → T₀ ≤ |s.im| → ‖zetaChi s‖ ≤ Cχ * (1 + |s.im|) ^ Nχ)
    (hζ : ∀ σ t : ℝ, |σ| ≤ 4 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ Nζ)
    {u T : ℝ} (hu1 : -(9 / 20) ≤ u) (hu2 : u ≤ -(1 / 4)) (hT : max T₀ 0 + |τ| + 1 ≤ T) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (Cχ * Cχ * Cζ * 2 ^ Nζ * max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (9 / 20 : ℝ))
          * Real.exp 1) * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hT1 : 1 ≤ T := by linarith [abs_nonneg τ, le_max_right T₀ 0]
  have hT0' : 0 ≤ T := by linarith
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hheight : ∀ σ : ℝ, |σ| ≤ |τ| → T₀ ≤ |σ - ε * T| ∧ |σ - ε * T| ≤ |τ| + T := by
    intro σ hσ
    have h1 : |σ - ε * T| ≤ |σ| + |ε * T| := abs_sub _ _
    have h2 : |ε * T| = T := by rw [abs_mul, hεabs, one_mul, abs_of_nonneg hT0']
    have h3 : |ε * T| - |σ| ≤ |σ - ε * T| := by
      have := abs_sub_abs_le_abs_sub (ε * T) σ
      rw [abs_sub_comm] at this
      linarith
    constructor
    · rw [h2] at h3; linarith [le_max_left T₀ 0]
    · rw [h2] at h1; linarith
  have hχbound : ∀ σ : ℝ, |σ| ≤ |τ| →
      ‖zetaChi (displacedLinePt d σ - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        ≤ Cχ * (1 + |τ| + T) ^ Nχ := by
    intro σ hσ
    obtain ⟨hlow, hup⟩ := hheight σ hσ
    have harg : displacedLinePt d σ - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)
        = ((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * T : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have h := hχ (((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * T : ℝ) : ℂ) * I)
      (by simp; linarith) (by simp; linarith) (by simp; exact hlow)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ hCχ
    apply pow_le_pow_left₀ (by positivity) _ Nχ
    linarith
  have h1 := hχbound τ le_rfl
  have h2 := hχbound (-τ) (by rw [abs_neg])
  have hp : ‖((c * x : ℝ) : ℂ) ^ (-((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (9 / 20 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hc hx)]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact rpow_le_max_of_mem_Icc (mul_pos hc hx) (by linarith) (by linarith)
  have hk := norm_smoothAFEGaussianKernel_horizontal_le (u := u) (T := T) (by linarith)
    (by linarith) hT1 hε
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ Cζ * 2 ^ Nζ * (1 + |τ| + T) ^ Nζ := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        = ((1 + 2 * d + 2 * u : ℝ) : ℂ) + ((2 * (ε * T) : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg]
    have h := hζ (1 + 2 * d + 2 * u) (2 * (ε * T)) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_nonneg hT0']; linarith)
    rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hT0',
      one_mul] at h
    refine h.trans ?_
    rw [mul_pow, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCζ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ hT0' _ Nζ
    linarith [abs_nonneg τ]
  have hpow : (1 + |τ| + T) ^ Nχ * (1 + |τ| + T) ^ Nχ * (1 + |τ| + T) ^ Nζ
      = (1 + |τ| + T) ^ (2 * Nχ + Nζ) := by
    rw [← pow_add, ← pow_add, two_mul]
  calc ‖zetaChi (displacedLinePt d τ - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ (Cχ * (1 + |τ| + T) ^ Nχ) * (Cχ * (1 + |τ| + T) ^ Nχ)
          * (max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (9 / 20 : ℝ))
            * (Real.exp 1 * Real.exp (-(T ^ 2))))
          * (Cζ * 2 ^ Nζ * (1 + |τ| + T) ^ Nζ) := by
        gcongr
    _ = (Cχ * Cχ * Cζ * 2 ^ Nζ * max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (9 / 20 : ℝ))
          * Real.exp 1) * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
        rw [← hpow]; ring

theorem tendsto_dualDiagonalIntegrand_horizontal_deep {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-(9 / 20) : ℝ)..(-(1 / 4) : ℝ),
      dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨T₀, Nχ, Cχ, hCχ, hχ⟩ := hasStripPolyGrowthOffReal_zetaChi (-1) 1
  obtain ⟨Cζ, Nζ, hCζ, hζ⟩ := exists_bound_norm_riemannZeta_strip 4
  set B : ℝ := Cχ * Cχ * Cζ * 2 ^ Nζ * max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (9 / 20 : ℝ))
    * Real.exp 1 with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ => ((1 / 5) * B) * ((1 + |τ| + T) ^ (2 * Nχ + Nζ)
      * Real.exp (-(T ^ 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 + |τ|) (2 * Nχ + Nζ)).const_mul ((1 / 5) * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max T₀ 0 + |τ| + 1)] with T hT
  have hbound : ∀ u ∈ Set.uIoc (-(9 / 20) : ℝ) (-(1 / 4) : ℝ),
      ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ B * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    exact norm_dualDiagonalIntegrand_horizontal_deep_le hd hd20 hc hx hCχ hCζ hχ hζ hu.1.le hu.2
      hT hε
  calc ‖∫ u : ℝ in (-(9 / 20) : ℝ)..(-(1 / 4) : ℝ),
        dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2)))
          * |(-(1 / 4) : ℝ) - (-(9 / 20))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ((1 / 5) * B) * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
        rw [show |(-(1 / 4) : ℝ) - (-(9 / 20))| = 1 / 5 by norm_num]
        ring

theorem differentiableOn_dualDiagonalIntegrand_deepStrip {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) :
    DifferentiableOn ℂ (dualDiagonalIntegrand d c x τ) (verticalStrip (-(9 / 20)) (-(1 / 4))) := by
  intro w hw
  rw [mem_verticalStrip] at hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith [hw.2]
  have hwre : -(1 / 2) - d < w.re := by linarith [hw.1]
  have hcar : AnalyticAt ℂ (carrierIntegrand d τ (c * x)) w :=
    ((analyticAt_zetaChi_displaced_sub d τ hwre).mul
      (analyticAt_zetaChi_displaced_sub d (-τ) hwre)).mul
      (analyticAt_smoothAFEMellinIntegrand (mul_pos hc hx) hw0)
  have hne : (((1 + 2 * d : ℝ) : ℂ) + 2 * w) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hw.2]
  have hz : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w)) w :=
    (differentiableAt_riemannZeta hne).comp w (by fun_prop)
  exact (hcar.differentiableAt.mul hz).differentiableWithinAt

/-- **The dual-diagonal remainder on the deep line.** -/
theorem dualLeft_eq_deep {d c x τ : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20) (hc : 0 < c)
    (hx : 0 < x) :
    dualLeft d c x τ = (1 / (2 * Real.pi)) •
      ∫ v : ℝ, dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I) := by
  unfold dualLeft
  congr 1
  have hbot := tendsto_dualDiagonalIntegrand_horizontal_deep (τ := τ) hd hd20 hc hx
    (ε := -1) (Or.inr rfl)
  have htop := tendsto_dualDiagonalIntegrand_horizontal_deep (τ := τ) hd hd20 hc hx
    (ε := 1) (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hbot htop
  exact integral_vertical_line_eq_of_horizontal_tendsto (by norm_num)
    (differentiableOn_dualDiagonalIntegrand_deepStrip hd hd20 hc hx)
    (integrable_dualDiagonalIntegrand_deep hd hd20 hc hx)
    (integrable_dualDiagonalIntegrand_left hd (by linarith) hc hx) hbot htop

/-- **`‖dualLeft‖ ≤ K₂ (cx)^{9/20} (1 + |τ|)^{−(9/10 − 2d)}`**, uniformly in `d ∈ (0, 1/20]`, `c`, `x`,
`τ`. -/
theorem exists_norm_dualLeft_le_deep :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x →
      ‖dualLeft d c x τ‖ ≤ K * (c * x) ^ (9 / 20 : ℝ) * (1 + |τ|) ^ (-(9 / 10 - 2 * d)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_rightStrip_deep
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hG0 : 0 ≤ ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) :=
    integral_nonneg fun v => by positivity
  refine ⟨(1 / (2 * Real.pi)) * (12 * Cχ * Cχ * Cζ * Real.exp (81 / 400)
    * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))), by positivity,
    fun d c x τ hd hd20 hc hx => ?_⟩
  rw [dualLeft_eq_deep hd hd20 hc hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hbound := fun v : ℝ =>
    norm_dualDiagonalIntegrand_deep_le (τ := τ) hd hd20 hc hx hCχ hCζ hχ hζ v
  set A : ℝ := (12 * Cχ * Cχ * Cζ * Real.exp (81 / 400)) * (c * x) ^ (9 / 20 : ℝ)
    * (1 + |τ|) ^ (-(9 / 10 - 2 * d)) with hAdef
  have hnorm : ‖∫ v : ℝ, dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ A * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) := by
    calc ‖∫ v : ℝ, dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)‖
        ≤ ∫ v : ℝ, ‖dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, A * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
            (integrable_one_add_abs_cube_mul_exp_neg_sq.const_mul A)
            (Filter.Eventually.of_forall fun v => hbound v)
      _ = A * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
  calc (1 / (2 * Real.pi))
        * ‖∫ v : ℝ, dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (A * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [hAdef]; ring

end RHTower.ZetaGateProductAFE
