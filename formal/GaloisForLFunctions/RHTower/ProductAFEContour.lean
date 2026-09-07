import GaloisForLFunctions.RHTower.ProductAFEIntegrand
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneral

/-!
# Contour shift for the product zeta Mellin integrand

The product integrand is `ζ(s₂+w)` times the single-zeta Gaussian Mellin integrand at `s₁`, so
every growth estimate of the degree-one theory multiplies by one polynomial factor.  On the
vertical lines `Re w = ±1` the integrand is integrable and the truncated integrals converge; the
horizontal Gaussian edges vanish.  Combining with the finite three-pole rectangle identity gives

  `(1/2πi) [ ∫_{(1)} − ∫_{(−1)} ] = ζ(s₁)ζ(s₂) + Res_{1−s₁} + Res_{1−s₂}`

for base points `s₁ ≠ s₂` in the strip `0 < Re s_i < 2`, `s_i ≠ 1`.
-/

noncomputable section

namespace RHTower

open Complex Set Filter Topology MeasureTheory

theorem productAFEIntegrand_eq_mul (s₁ s₂ : ℂ) (x : ℝ) (w : ℂ) :
    productAFEIntegrand s₁ s₂ x w =
      riemannZeta (s₂ + w) * smoothAFEZetaMellinIntegrand s₁ x w := by
  unfold productAFEIntegrand smoothAFEZetaMellinIntegrand
  ring

/-! ## Vertical lines -/

theorem norm_riemannZeta_vertical_shift_le {s : ℂ} {c : ℝ} {C : ℝ} (hC0 : 0 ≤ C) {N : ℕ}
    (hC : ∀ t : ℝ, ‖riemannZeta (((s.re + c : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N)
    (v : ℝ) :
    ‖riemannZeta (s + ((c : ℂ) + (v : ℂ) * I))‖ ≤ C * ((1 + |s.im|) + |v|) ^ N := by
  rw [smoothAFEZetaMellinIntegrand_vertical_point]
  refine le_trans (hC (s.im + v)) ?_
  have hmono : (1 + |s.im + v|) ^ N ≤ ((1 + |s.im|) + |v|) ^ N := by
    refine pow_le_pow_left₀ (by positivity) ?_ N
    have := abs_add_le s.im v
    linarith
  exact mul_le_mul_of_nonneg_left hmono hC0

theorem norm_productAFEIntegrand_vertical_le {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ} {c : ℝ}
    (hc : c ≠ 0) {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) {N₁ N₂ : ℕ}
    (hC₁ : ∀ t : ℝ, ‖riemannZeta (((s₁.re + c : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (1 + |t|) ^ N₁)
    (hC₂ : ∀ t : ℝ, ‖riemannZeta (((s₂.re + c : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (1 + |t|) ^ N₂)
    (v : ℝ) :
    ‖productAFEIntegrand s₁ s₂ x ((c : ℂ) + (v : ℂ) * I)‖
      ≤ (C₂ * (C₁ * (x ^ c * (Real.exp (c ^ 2) / |c|))))
        * (((2 + |s₁.im| + |s₂.im|) + |v|) ^ (N₁ + N₂) * Real.exp (-v ^ 2)) := by
  rw [productAFEIntegrand_eq_mul, norm_mul]
  have h1 := norm_smoothAFEZetaMellinIntegrand_vertical_general_le hx hc hC₁0 hC₁ v
  have h2 := norm_riemannZeta_vertical_shift_le hC₂0 hC₂ v
  have hprod : ((1 + |s₂.im|) + |v|) ^ N₂ * ((1 + |s₁.im|) + |v|) ^ N₁
      ≤ ((2 + |s₁.im| + |s₂.im|) + |v|) ^ (N₁ + N₂) := by
    rw [add_comm N₁ N₂, pow_add]
    exact mul_le_mul
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s₁.im]) N₂)
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s₂.im]) N₁)
      (by positivity) (by positivity)
  have hK : (0 : ℝ) ≤ C₂ * (C₁ * (x ^ c * (Real.exp (c ^ 2) / |c|))) := by
    have := Real.rpow_pos_of_pos hx c
    positivity
  calc ‖riemannZeta (s₂ + ((c : ℂ) + (v : ℂ) * I))‖
        * ‖smoothAFEZetaMellinIntegrand s₁ x ((c : ℂ) + (v : ℂ) * I)‖
      ≤ (C₂ * ((1 + |s₂.im|) + |v|) ^ N₂)
        * ((C₁ * (x ^ c * (Real.exp (c ^ 2) / |c|)))
          * (((1 + |s₁.im|) + |v|) ^ N₁ * Real.exp (-v ^ 2))) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = (C₂ * (C₁ * (x ^ c * (Real.exp (c ^ 2) / |c|))))
        * ((((1 + |s₂.im|) + |v|) ^ N₂ * ((1 + |s₁.im|) + |v|) ^ N₁) * Real.exp (-v ^ 2)) := by
        ring
    _ ≤ _ :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) hK

theorem continuous_riemannZeta_vertical_shift {s : ℂ} {c : ℝ} (hsc : s.re + c ≠ 1) :
    Continuous fun v : ℝ => riemannZeta (s + ((c : ℂ) + (v : ℂ) * I)) := by
  have hne1 : ∀ v : ℝ, s + ((c : ℂ) + (v : ℂ) * I) ≠ 1 := by
    intro v h
    rw [smoothAFEZetaMellinIntegrand_vertical_point] at h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re] at hre
    exact hsc (by linarith)
  refine continuous_iff_continuousAt.mpr fun v => ?_
  have hc1 : ContinuousAt (fun u : ℝ => s + ((c : ℂ) + (u : ℂ) * I)) v := by fun_prop
  have hc2 : ContinuousAt riemannZeta (s + ((c : ℂ) + (v : ℂ) * I)) :=
    (differentiableAt_riemannZeta (hne1 v)).continuousAt
  have hcomp : ContinuousAt (riemannZeta ∘ fun u : ℝ => s + ((c : ℂ) + (u : ℂ) * I)) v :=
    ContinuousAt.comp hc2 hc1
  simpa [Function.comp_def] using hcomp

theorem continuous_productAFEIntegrand_vertical {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ} {c : ℝ}
    (hc : c ≠ 0) (h₁ : s₁.re + c ≠ 1) (h₂ : s₂.re + c ≠ 1) :
    Continuous fun v : ℝ => productAFEIntegrand s₁ s₂ x ((c : ℂ) + (v : ℂ) * I) := by
  simp only [productAFEIntegrand_eq_mul]
  exact (continuous_riemannZeta_vertical_shift h₂).mul
    (continuous_smoothAFEZetaMellinIntegrand_vertical hx hc h₁)

/-- **Vertical integrability of the product integrand** off the two pole abscissae. -/
theorem productAFEIntegrand_verticalIntegrable {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ} {c : ℝ}
    (hc : c ≠ 0) (h₁ : s₁.re + c ≠ 1) (h₂ : s₂.re + c ≠ 1) :
    Complex.VerticalIntegrable (productAFEIntegrand s₁ s₂ x) c := by
  obtain ⟨C₁, N₁, hC₁0, hC₁⟩ := exists_bound_norm_riemannZeta_vertical (s₁.re + c) h₁
  obtain ⟨C₂, N₂, hC₂0, hC₂⟩ := exists_bound_norm_riemannZeta_vertical (s₂.re + c) h₂
  rw [Complex.VerticalIntegrable]
  refine Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (2 + |s₁.im| + |s₂.im|) (N₁ + N₂)).const_mul
      (C₂ * (C₁ * (x ^ c * (Real.exp (c ^ 2) / |c|)))))
    (continuous_productAFEIntegrand_vertical hx hc h₁ h₂).aestronglyMeasurable ?_
  filter_upwards with v
  exact norm_productAFEIntegrand_vertical_le hx hc hC₁0 hC₂0 hC₁ hC₂ v

theorem tendsto_productAFEIntegrand_vertical {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ} {c : ℝ}
    (hc : c ≠ 0) (h₁ : s₁.re + c ≠ 1) (h₂ : s₂.re + c ≠ 1) :
    Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T, productAFEIntegrand s₁ s₂ x ((c : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (∫ v : ℝ, productAFEIntegrand s₁ s₂ x ((c : ℂ) + (v : ℂ) * I))) :=
  intervalIntegral_tendsto_integral (productAFEIntegrand_verticalIntegrable hx hc h₁ h₂)
    tendsto_neg_atTop_atBot tendsto_id

/-! ## Horizontal edges -/

theorem norm_riemannZeta_horizontal_shift_le (s : ℂ) {C : ℝ} (hC0 : 0 ≤ C) {N : ℕ}
    (hC : ∀ σ t : ℝ, |σ| ≤ |s.re| + 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {u v : ℝ} (huLow : -1 ≤ u) (huHigh : u ≤ 1) (hv : |s.im| + 1 ≤ |v|) :
    ‖riemannZeta (s + ((u : ℂ) + (v : ℂ) * I))‖ ≤ C * (|s.im| + |v|) ^ N := by
  set w : ℂ := (u : ℂ) + (v : ℂ) * I with hw
  have hwre : w.re = u := by rw [hw]; simp
  have hwim : w.im = v := by rw [hw]; simp
  have hsre : (s + w).re = s.re + u := by rw [Complex.add_re, hwre]
  have hsim : (s + w).im = s.im + v := by rw [Complex.add_im, hwim]
  have hrec : ((((s + w).re : ℝ)) : ℂ) + (((s + w).im : ℝ) : ℂ) * I = s + w :=
    Complex.re_add_im _
  have hreabs : |(s + w).re| ≤ |s.re| + 1 := by
    rw [hsre]
    have h1 : |s.re + u| ≤ |s.re| + |u| := abs_add_le _ _
    have h2 : |u| ≤ 1 := abs_le.mpr ⟨huLow, huHigh⟩
    linarith
  have himabs : |(s + w).im| ≤ |s.im| + |v| := by
    rw [hsim]
    exact abs_add_le _ _
  have himge : (1 : ℝ) ≤ |(s + w).im| := by
    rw [hsim]
    have h1 : |v| - |s.im| ≤ |s.im + v| := by
      have h := abs_sub_abs_le_abs_sub v (-s.im)
      simp only [abs_neg, sub_neg_eq_add] at h
      rw [add_comm v s.im] at h
      linarith [h]
    linarith
  have hbase := hC (s + w).re (s + w).im hreabs himge
  rw [hrec] at hbase
  refine le_trans hbase ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) himabs N) hC0

theorem norm_productAFEIntegrand_horizontal_le {x : ℝ} (hx : 0 < x) (s₁ s₂ : ℂ)
    {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) {N₁ N₂ : ℕ}
    (hC₁ : ∀ σ t : ℝ, |σ| ≤ |s₁.re| + 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * |t| ^ N₁)
    (hC₂ : ∀ σ t : ℝ, |σ| ≤ |s₂.re| + 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * |t| ^ N₂)
    {u v : ℝ} (huLow : -1 ≤ u) (huHigh : u ≤ 1) (hv : |s₁.im| + |s₂.im| + 1 ≤ |v|) :
    ‖productAFEIntegrand s₁ s₂ x ((u : ℂ) + (v : ℂ) * I)‖
      ≤ (C₂ * (C₁ * max x x⁻¹ * Real.exp 1))
        * (((|s₁.im| + |s₂.im|) + |v|) ^ (N₁ + N₂) * Real.exp (-(v ^ 2))) := by
  have hv₁ : |s₁.im| + 1 ≤ |v| := by linarith [abs_nonneg s₂.im]
  have hv₂ : |s₂.im| + 1 ≤ |v| := by linarith [abs_nonneg s₁.im]
  rw [productAFEIntegrand_eq_mul, norm_mul]
  have h1 := norm_smoothAFEZetaMellinIntegrand_general_le hx s₁ hC₁0 hC₁ huLow huHigh hv₁
  have h2 := norm_riemannZeta_horizontal_shift_le s₂ hC₂0 hC₂ huLow huHigh hv₂
  have hprod : (|s₂.im| + |v|) ^ N₂ * (|s₁.im| + |v|) ^ N₁
      ≤ ((|s₁.im| + |s₂.im|) + |v|) ^ (N₁ + N₂) := by
    rw [add_comm N₁ N₂, pow_add]
    exact mul_le_mul
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s₁.im]) N₂)
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s₂.im]) N₁)
      (by positivity) (by positivity)
  have hmax : (0 : ℝ) ≤ max x x⁻¹ := le_trans hx.le (le_max_left _ _)
  have hK : (0 : ℝ) ≤ C₂ * (C₁ * max x x⁻¹ * Real.exp 1) := by positivity
  calc ‖riemannZeta (s₂ + ((u : ℂ) + (v : ℂ) * I))‖
        * ‖smoothAFEZetaMellinIntegrand s₁ x ((u : ℂ) + (v : ℂ) * I)‖
      ≤ (C₂ * (|s₂.im| + |v|) ^ N₂)
        * ((C₁ * max x x⁻¹ * Real.exp 1) * ((|s₁.im| + |v|) ^ N₁ * Real.exp (-(v ^ 2)))) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = (C₂ * (C₁ * max x x⁻¹ * Real.exp 1))
        * (((|s₂.im| + |v|) ^ N₂ * (|s₁.im| + |v|) ^ N₁) * Real.exp (-(v ^ 2))) := by ring
    _ ≤ _ :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) hK

/-- **The horizontal Gaussian edges vanish.**  `ε = 1` is the top edge, `ε = -1` the bottom. -/
theorem tendsto_productAFEIntegrand_horizontal {x : ℝ} (hx : 0 < x) (s₁ s₂ : ℂ) {ε : ℝ}
    (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-1)..1,
        productAFEIntegrand s₁ s₂ x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C₁, N₁, hC₁0, hC₁⟩ := exists_bound_norm_riemannZeta_strip (|s₁.re| + 1)
  obtain ⟨C₂, N₂, hC₂0, hC₂⟩ := exists_bound_norm_riemannZeta_strip (|s₂.re| + 1)
  set a : ℝ := |s₁.im| + |s₂.im| with ha
  set K : ℝ := C₂ * (C₁ * max x x⁻¹ * Real.exp 1) with hK
  have hmax : (0 : ℝ) ≤ max x x⁻¹ := le_trans hx.le (le_max_left _ _)
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hlim : Tendsto (fun T : ℝ => 2 * (K * ((a + T) ^ (N₁ + N₂) * Real.exp (-(T ^ 2)))))
      atTop (𝓝 0) := by
    have h := (tendsto_shifted_pow_mul_exp_neg_sq a (N₁ + N₂)).const_mul K
    simpa using h.const_mul (2 : ℝ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (a + 1)] with T hT
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hT0 : (0 : ℝ) < T := by linarith
  have habsv : |ε * T| = T := by
    rw [abs_mul, hε, one_mul, abs_of_pos hT0]
  have hpoint : ∀ u ∈ Set.uIoc (-1 : ℝ) 1,
      ‖productAFEIntegrand s₁ s₂ x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ K * ((a + T) ^ (N₁ + N₂) * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    have hbound := norm_productAFEIntegrand_horizontal_le hx s₁ s₂ hC₁0 hC₂0 hC₁ hC₂
      (u := u) (v := ε * T) hu.1.le hu.2 (by rw [habsv]; linarith)
    rw [habsv] at hbound
    have hsq : (ε * T) ^ 2 = T ^ 2 := by
      have : (ε * T) ^ 2 = ε ^ 2 * T ^ 2 := by ring
      rw [this, show ε ^ 2 = |ε| ^ 2 by rw [sq_abs], hε]
      ring
    rw [hsq] at hbound
    exact hbound
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have habs : |(1 : ℝ) - (-1)| = 2 := by norm_num
  rw [habs] at h
  calc ‖∫ u : ℝ in (-1 : ℝ)..1,
        productAFEIntegrand s₁ s₂ x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ K * ((a + T) ^ (N₁ + N₂) * Real.exp (-(T ^ 2))) * 2 := h
    _ = 2 * (K * ((a + T) ^ (N₁ + N₂) * Real.exp (-(T ^ 2)))) := by ring

/-! ## The finite and infinite contour identities -/

theorem rectIntegral_productAFEIntegrand_horizontal_box {s₁ s₂ : ℂ} {x a b T : ℝ}
    (hx : 0 < x) (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 1) (hne : s₁ ≠ s₂)
    (ha0 : a < 0) (h0b : 0 < b) (hT : 0 < T)
    (hρa : a < (1 - s₁).re) (hρb : (1 - s₁).re < b)
    (hρlow : -T < (1 - s₁).im) (hρhigh : (1 - s₁).im < T)
    (hσa : a < (1 - s₂).re) (hσb : (1 - s₂).re < b)
    (hσlow : -T < (1 - s₂).im) (hσhigh : (1 - s₂).im < T) :
    rectIntegral (productAFEIntegrand s₁ s₂ x) ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) =
      2 * Real.pi * I * (riemannZeta s₁ * riemannZeta s₂ +
        productAFEShiftedResidue s₁ s₂ x + productAFEShiftedResidue s₂ s₁ x) := by
  apply rectIntegral_productAFEIntegrand_eq hx h₁ h₂ hne
  · simpa using ha0
  · simpa using h0b
  · simpa using hT
  · simpa using hT
  · simpa using hρa
  · simpa using hρb
  · simpa using hρlow
  · simpa using hρhigh
  · simpa using hσa
  · simpa using hσb
  · simpa using hσlow
  · simpa using hσhigh

/-- **The finite two-pole-free rectangle identity on `[-1, 1] × [-T, T]`.** -/
theorem productAFE_finite_contour_shift {x T : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 1) (hne : s₁ ≠ s₂)
    (hre₁0 : 0 < s₁.re) (hre₁2 : s₁.re < 2) (hre₂0 : 0 < s₂.re) (hre₂2 : s₂.re < 2)
    (hT₁ : |s₁.im| < T) (hT₂ : |s₂.im| < T) :
    ((∫ u : ℝ in (-1)..1, productAFEIntegrand s₁ s₂ x ((u : ℂ) - (T : ℂ) * I)) -
        (∫ u : ℝ in (-1)..1, productAFEIntegrand s₁ s₂ x ((u : ℂ) + (T : ℂ) * I)) +
      I • (∫ v : ℝ in (-T)..T, productAFEIntegrand s₁ s₂ x ((1 : ℂ) + (v : ℂ) * I))) -
      I • (∫ v : ℝ in (-T)..T, productAFEIntegrand s₁ s₂ x ((-1 : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I * (riemannZeta s₁ * riemannZeta s₂ +
        productAFEShiftedResidue s₁ s₂ x + productAFEShiftedResidue s₂ s₁ x) := by
  have hTpos : 0 < T := lt_of_le_of_lt (abs_nonneg _) hT₁
  have hρre : (1 - s₁).re = 1 - s₁.re := by simp
  have hρim : (1 - s₁).im = -s₁.im := by simp
  have hσre : (1 - s₂).re = 1 - s₂.re := by simp
  have hσim : (1 - s₂).im = -s₂.im := by simp
  have habs₁ := abs_lt.mp hT₁
  have habs₂ := abs_lt.mp hT₂
  have hbox := rectIntegral_productAFEIntegrand_horizontal_box
    (s₁ := s₁) (s₂ := s₂) (x := x) (a := -1) (b := 1) (T := T)
    hx h₁ h₂ hne (by norm_num) (by norm_num) hTpos
    (by rw [hρre]; linarith) (by rw [hρre]; linarith)
    (by rw [hρim]; linarith) (by rw [hρim]; linarith)
    (by rw [hσre]; linarith) (by rw [hσre]; linarith)
    (by rw [hσim]; linarith) (by rw [hσim]; linarith)
  simpa [rectIntegral] using! hbox

/-- **The infinite two-line contour identity for the product integrand.** -/
theorem productAFE_infinite_contour_shift {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 1) (hne : s₁ ≠ s₂)
    (hre₁0 : 0 < s₁.re) (hre₁2 : s₁.re < 2) (hre₂0 : 0 < s₂.re) (hre₂2 : s₂.re < 2) :
    I • (∫ v : ℝ, productAFEIntegrand s₁ s₂ x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ, productAFEIntegrand s₁ s₂ x (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I * (riemannZeta s₁ * riemannZeta s₂ +
        productAFEShiftedResidue s₁ s₂ x + productAFEShiftedResidue s₂ s₁ x) := by
  set F : ℂ → ℂ := productAFEIntegrand s₁ s₂ x with hF
  have hr1 : s₁.re + (1 : ℝ) ≠ 1 := by intro h; linarith
  have hr2 : s₂.re + (1 : ℝ) ≠ 1 := by intro h; linarith
  have hl1 : s₁.re + (-1 : ℝ) ≠ 1 := by intro h; linarith
  have hl2 : s₂.re + (-1 : ℝ) ≠ 1 := by intro h; linarith
  have hright := tendsto_productAFEIntegrand_vertical (x := x) hx (c := (1 : ℝ)) (by norm_num)
    hr1 hr2
  have hleft := tendsto_productAFEIntegrand_vertical (x := x) hx (c := (-1 : ℝ)) (by norm_num)
    hl1 hl2
  have htop0 := tendsto_productAFEIntegrand_horizontal hx s₁ s₂ (ε := (1 : ℝ)) (by norm_num)
  have hbot0 := tendsto_productAFEIntegrand_horizontal hx s₁ s₂ (ε := (-1 : ℝ)) (by norm_num)
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine htop0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hbottom : Tendsto (fun T : ℝ => ∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine hbot0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝 (I • (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [hF] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * (riemannZeta s₁ * riemannZeta s₂ +
          productAFEShiftedResidue s₁ s₂ x + productAFEShiftedResidue s₂ s₁ x) := by
    filter_upwards [eventually_gt_atTop |s₁.im|, eventually_gt_atTop |s₂.im|] with T hT₁ hT₂
    simpa [hF] using productAFE_finite_contour_shift hx h₁ h₂ hne hre₁0 hre₁2 hre₂0 hre₂2 hT₁ hT₂
  exact tendsto_nhds_unique (hlimit'.congr' hevent) tendsto_const_nhds

end RHTower

end
