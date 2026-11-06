import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheQuotientByAnIsolatedZero
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheExceptionalSetHasAPowerSaving
import GaloisForLFunctions.RHTower.DeBruijnNewmanEnergyTransition
import GaloisForLFunctions.HTGeometry.DiscHolomorphicFixedPoint

/-!
# The sharp depth law

A simple zero `ρ = ½ + d + it` of `ζ` without a crowd survives the de Bruijn flow until `τ log(t/2π) = d`, and no longer:

`d − 7η ≤ Λ_X log(X/2π) ≤ d + 17η`    (`localNewman_scaled_mem_Icc`).

So the linear depth law holds outside crowds with the sharp constant `1`, and without the logarithmic loss of the
potential method.

The upper bound is `eventually_localNewmanConstant_le_of_depthWindow`. The lower bound comes from one exact identity.
Let `Λ = c ξ/(s − ρ)` and let `𝓖(z) = ∫ g_τ(u) Λ(½ + iz + u) du` be its Gaussian average, `D` its first moment:

`c H_τ(z) = (½ + iz − ρ) 𝓖(z) + 2τ D(z)`.

So `H_τ` vanishes exactly at the fixed points of the holomorphic map `ψ(z) = z + i c H_τ(z)/𝓖(z)`, and

`½ + iψ(z) = ρ − 2τ D(z)/𝓖(z)`.

The function `Λ` has no zero near `ρ`, so the complex saddle applies to it on a fixed disc: `𝓖` does not vanish there and
`D/𝓖` is the horizontal slope up to `O(η/τ)`. Hence `ψ` maps the disc about `½ + iz₀ = ρ − 2τ a(t)` into its concentric half,
and the disc fixed point theorem produces the zero of `H_τ` (`exists_riemannHeat_eq_zero_near`).
-/

set_option autoImplicit false

open Complex Set Metric Filter Topology MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ## The Gaussian average of an entire function is entire -/

/-- The Gaussian horizontal average of `f`. -/
def gaussAverage (f : ℂ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (gaussDensity τ u : ℂ) * f (1 / 2 + I * z + u)

/-- Below the growth horizon `8Sτ < 1`, the Gaussian average of an entire function is entire. -/
theorem differentiable_gaussAverage {f : ℂ → ℂ} (hf : Differentiable ℂ f) {τ C S : ℝ} (hτ : 0 < τ)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hτS : 8 * S * τ < 1)
    (hb : ∀ z : ℂ, ‖f (1 / 2 + I * z)‖ ≤ C * Real.exp (S * ‖z‖ ^ 2)) :
    Differentiable ℂ (gaussAverage f τ) := by
  intro z₀
  obtain ⟨A, hA⟩ : ∃ A, A = ‖z₀‖ + 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  obtain ⟨M, hMdef⟩ : ∃ M, M = C * Real.exp (2 * S * A ^ 2) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    positivity
  have hpt : ∀ (q : ℂ) (u : ℝ), ‖q - 1 / 2‖ ≤ A + |u| → ‖f q‖ ≤ M * Real.exp (2 * S * u ^ 2) := by
    intro q u hq
    have hrep : (1 / 2 + I * (-I * (q - 1 / 2)) : ℂ) = q := by
      linear_combination (-(q - 1 / 2)) * Complex.I_sq
    have hn : ‖-I * (q - 1 / 2)‖ = ‖q - 1 / 2‖ := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have hb' := hb (-I * (q - 1 / 2))
    rw [hrep, hn] at hb'
    refine hb'.trans ?_
    rw [hMdef, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    have h0 := norm_nonneg (q - 1 / 2)
    have hsq := pow_le_pow_left₀ h0 hq 2
    have hab := abs_nonneg u
    have hu : |u| ^ 2 = u ^ 2 := sq_abs u
    have h2 : ‖q - 1 / 2‖ ^ 2 ≤ 2 * A ^ 2 + 2 * u ^ 2 := by
      nlinarith only [hsq, sq_nonneg (A - |u|), hu]
    nlinarith only [mul_le_mul_of_nonneg_left h2 hS]
  have hnorm : ∀ (z : ℂ) (u : ℝ), ‖z - z₀‖ < 1 → ‖(1 / 2 + I * z + u : ℂ) - 1 / 2‖ ≤ ‖z₀‖ + 1 + |u| := by
    intro z u hz
    have he : (1 / 2 + I * z + u : ℂ) - 1 / 2 = I * z + u := by ring
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have := norm_le_norm_add_norm_sub' z z₀
    linarith only [this, hz]
  have hgpos := fun u : ℝ => gaussDensity_pos hτ u
  have hcontF : ∀ z : ℂ, Continuous fun u : ℝ => (gaussDensity τ u : ℂ) * f (1 / 2 + I * z + u) := fun z =>
    (Complex.continuous_ofReal.comp (continuous_gaussDensity τ)).mul (hf.continuous.comp (by fun_prop))
  have hdf := differentiable_deriv_of_differentiable hf
  have hint := (integrable_gaussDensity_mul_exp_sq hτ hτS).const_mul M
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (z : ℂ) (u : ℝ) => (gaussDensity τ u : ℂ) * f (1 / 2 + I * z + u))
    (F' := fun (z : ℂ) (u : ℝ) => (gaussDensity τ u : ℂ) * (deriv f (1 / 2 + I * z + u) * I))
    (x₀ := z₀) (bound := fun u => M * (gaussDensity τ u * Real.exp (2 * S * u ^ 2)))
    (s := ball z₀ 1) (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hcontF z).aestronglyMeasurable) ?_ ?_ ?_ hint ?_
  · exact hkey.2.differentiableAt
  · refine hint.mono' (hcontF z₀).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hgpos u).le]
    have hq := hnorm z₀ u (by simp)
    have h1 := hpt _ u (hq.trans (by rw [hA]; linarith only))
    calc
      _ ≤ gaussDensity τ u * (M * Real.exp (2 * S * u ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (hgpos u).le
      _ = _ := by ring
  · exact ((Complex.continuous_ofReal.comp (continuous_gaussDensity τ)).mul
      ((hdf.continuous.comp (by fun_prop)).mul continuous_const)).aestronglyMeasurable
  · refine Eventually.of_forall fun u z hz => ?_
    rw [mem_ball, dist_eq_norm] at hz
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hgpos u).le]
    have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (1 / 2 + I * z + u : ℂ))
      (f := f) (R := 1) one_pos (hf.diffContOnCl) (C := M * Real.exp (2 * S * u ^ 2)) (fun q hq => by
        rw [mem_sphere_iff_norm] at hq
        refine hpt q u ?_
        have htri := norm_sub_le_norm_sub_add_norm_sub q (1 / 2 + I * z + u : ℂ) (1 / 2)
        have := hnorm z u hz
        rw [hA]
        linarith only [htri, hq, this])
    rw [div_one] at hC
    calc
      _ ≤ gaussDensity τ u * (M * Real.exp (2 * S * u ^ 2)) :=
        mul_le_mul_of_nonneg_left hC (hgpos u).le
      _ = _ := by ring
  · refine Eventually.of_forall fun u z _ => ?_
    have hin : HasDerivAt (fun z : ℂ => (1 / 2 + I * z + u : ℂ)) I z := by
      have h1 := ((hasDerivAt_id' z).const_mul I).const_add (1 / 2)
      rw [mul_one] at h1
      exact h1.add_const (u : ℂ)
    exact ((hf (1 / 2 + I * z + u)).hasDerivAt.comp z hin).const_mul (gaussDensity τ u : ℂ)

/-- `H_0` is bounded by `|ξ(½)| e^{S|w|²}`. -/
theorem norm_riemannHeat_zero_le_exp_sq (w : ℂ) :
    ‖riemannHeat 0 w‖ ≤ ‖XiC 0‖ * Real.exp (xiApproxGrowth * ‖w‖ ^ 2) :=
  le_of_tendsto' ((TendstoLocallyUniformly.tendstoLocallyUniformlyOn tendstoLocallyUniformly_xiRealApprox
    (s := Set.univ)).tendsto_at (Set.mem_univ w)).norm (fun n => norm_eval_map_xiRealApprox_le n w)

/-! ## The full-line average and moment -/

/-- The Gaussian average on the line at height `X`, centred at `y`. -/
def fullAvg (Λ : ℂ → ℂ) (τ X y : ℝ) : ℂ := ∫ w : ℝ, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w

/-- The first moment on the line at height `X`, centred at `y`. -/
def fullMoment (Λ : ℂ → ℂ) (τ X y : ℝ) : ℂ :=
  ∫ w : ℝ, (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn Λ X w

private theorem point_shift (X y w : ℝ) :
    (1 / 2 + I * ((X : ℂ) - I * y) + ((w - y : ℝ) : ℂ) : ℂ) = 1 / 2 + (w : ℂ) + I * X := by
  push_cast
  linear_combination (-(y : ℂ)) * Complex.I_sq

theorem gaussAverage_eq_fullAvg (Λ : ℂ → ℂ) (τ X y : ℝ) :
    gaussAverage Λ τ ((X : ℂ) - I * y) = fullAvg Λ τ X y := by
  unfold gaussAverage fullAvg
  rw [← integral_sub_right_eq_self
    (fun u : ℝ => (gaussDensity τ u : ℂ) * Λ (1 / 2 + I * ((X : ℂ) - I * y) + u)) y]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [point_shift]
  rfl

theorem riemannHeat_eq_fullAvg_xi {τ : ℝ} (hτ : 0 < τ) (X y : ℝ) :
    riemannHeat τ ((X : ℂ) - I * y) = fullAvg xi τ X y := by
  rw [riemannHeat_eq_integral_gaussian_xi hτ]
  exact gaussAverage_eq_fullAvg xi τ X y

/-- The error of the reflected half. -/
def reflectErr (K B τ α y : ℝ) : ℝ :=
  K * Real.exp 1 * Real.exp (-(2 * y * α) + τ * (B + 1 / 8) ^ 2)

namespace PowerSaddle

variable {Λ : ℂ → ℂ} {d η B K t X τ y a δ : ℝ} {ℓ : ℂ}

theorem mass_pos (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) : 0 < SaddleData.mass (lineF Λ X) τ a δ ℓ := by
  have hη := h.hη
  have hXt := abs_le.mp h.hXt
  have hδ := abs_le.mp h.hδ
  have hreg : (a : ℂ) + (δ : ℂ) * I ∈ saddleRegion d η t X := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
      linarith only [h.ha1, hη]
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
      linarith only [h.ha2]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
      exact abs_le.mpr ⟨by linarith only [hXt.1, hδ.1, hη], by linarith only [hXt.2, hδ.2, hη]⟩
  have hne := h.model.ne_zero h.hX (h.hXt.trans (by linarith only [hη])) hreg
  exact mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)

theorem integrable_left (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    Integrable (fun w => gaussDensity τ (w + y) * ‖lineFn Λ X w‖) := by
  have hi := (integrable_gaussDensity_sub_mul h.hτ (h.model.continuous_lineFn X)
    (h.model.integrable h.hτ) (-y)).norm
  refine hi.congr (Eventually.of_forall fun w => ?_)
  have hn := norm_gauss_mul τ (-y) w h.hτ (lineFn Λ X w)
  simp only [sub_neg_eq_add] at hn
  simp only [sub_neg_eq_add]
  exact hn

/-- The reflected half has mass at most `P (reflectErr + far)`. -/
theorem left_mass_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) (hy : 0 ≤ y) :
    (∫ w in Ioi (0 : ℝ), gaussDensity τ (w + y) * ‖lineFn Λ X w‖) ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ *
        (reflectErr K B τ (horizontalSlope X).re y + powerFar K B τ (horizontalSlope X).re) := by
  obtain ⟨hW9, _⟩ := h.hW
  have hW0 : 0 ≤ 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := by
    linarith only [hW9]
  have hint := h.integrable_left
  have hunion := setIntegral_union (μ := volume)
    (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ))
      (b := 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2))
    measurableSet_Ioi hint.integrableOn hint.integrableOn
  rw [Ioc_union_Ioi_eq_Ioi hW0] at hunion
  rw [hunion, mul_add]
  exact add_le_add (h.opposite_range_le hy) (h.opposite_far_le hy)

/-- The reflected half with the moment weight. -/
theorem left_weight_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) (hy : 0 ≤ y) :
    (∫ w in Ioi (0 : ℝ), (|(w + y) / (2 * τ)| + ‖horizontalSlope X‖) * gaussDensity τ (w + y) *
        ‖lineFn Λ X w‖) ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ *
        (((2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) / (2 * τ) +
          ‖horizontalSlope X‖) * reflectErr K B τ (horizontalSlope X).re y +
          2 * powerFar K B τ (horizontalSlope X).re) := by
  have hτ := h.hτ
  have h2τ : 0 < 2 * τ := by positivity
  obtain ⟨hW9, _⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW9 ⊢
  have hW0 : 0 ≤ W := by linarith only [hW9]
  have hweight := integrable_weight h.model hτ X (-y) ‖horizontalSlope X‖
  simp only [sub_neg_eq_add] at hweight
  have hunion := setIntegral_union (μ := volume)
    (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := W))
    measurableSet_Ioi hweight.integrableOn hweight.integrableOn
  rw [Ioc_union_Ioi_eq_Ioi hW0] at hunion
  rw [hunion]
  obtain ⟨P, hPdef⟩ : ∃ P, P = SaddleData.mass (lineF Λ X) τ a δ ℓ := ⟨_, rfl⟩
  rw [← hPdef]
  have hΩ0 : 0 ≤ (W + 1) / (2 * τ) + ‖horizontalSlope X‖ := by positivity
  have hrange := h.opposite_range_le hy
  rw [← hWdef, ← hPdef] at hrange
  have hfar := h.far_terms_le.1
  rw [← hWdef, ← hPdef] at hfar
  have h1 : (∫ w in Ioc (0 : ℝ) W, (|(w + y) / (2 * τ)| + ‖horizontalSlope X‖) *
      gaussDensity τ (w + y) * ‖lineFn Λ X w‖) ≤
      ((W + 1) / (2 * τ) + ‖horizontalSlope X‖) *
        ∫ w in Ioc (0 : ℝ) W, gaussDensity τ (w + y) * ‖lineFn Λ X w‖ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hweight.integrableOn (h.integrable_left.const_mul _).integrableOn
      measurableSet_Ioc fun w hw => ?_
    have hg := (gaussDensity_pos hτ (w + y)).le
    have hle : |(w + y) / (2 * τ)| ≤ (W + 1) / (2 * τ) := by
      rw [abs_div, abs_of_pos h2τ]
      refine div_le_div_of_nonneg_right ?_ h2τ.le
      rw [abs_of_nonneg (by linarith only [hw.1, hy])]
      linarith only [hw.2, h.hy2]
    have hfac := mul_nonneg hg (norm_nonneg (lineFn Λ X w))
    calc
      _ = (|(w + y) / (2 * τ)| + ‖horizontalSlope X‖) *
          (gaussDensity τ (w + y) * ‖lineFn Λ X w‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hle]) hfac
  have h2 : (∫ w in Ioi W, (|(w + y) / (2 * τ)| + ‖horizontalSlope X‖) *
      gaussDensity τ (w + y) * ‖lineFn Λ X w‖) ≤
      2 * ∫ w in Ioi W, (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) *
        gaussDensity τ (w - y) * ‖lineFn Λ X w‖ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hweight.integrableOn
      ((integrable_weight h.model hτ X y ‖horizontalSlope X‖).const_mul 2).integrableOn
      measurableSet_Ioi fun w hw => ?_
    have hw' : W < w := hw
    have hwy : 3 * y ≤ w := by linarith only [hw', hW9, h.hy2]
    have hg := gaussDensity_add_le_of_lower_bound (b := 0) hτ hy (hW0.trans hw'.le)
    simp only [zero_mul, zero_div, neg_zero, Real.exp_zero, one_mul] at hg
    have hg0 := (gaussDensity_pos hτ (w + y)).le
    have hle : |(w + y) / (2 * τ)| ≤ 2 * |(w - y) / (2 * τ)| := by
      rw [abs_div, abs_div, abs_of_pos h2τ, abs_of_nonneg (by linarith only [hw', hW9, hy]),
        abs_of_nonneg (by linarith only [hw', hW9, h.hy2]), ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith only [hwy]) h2τ.le
    have hN := norm_nonneg (lineFn Λ X w)
    have hs0 := norm_nonneg (horizontalSlope X)
    have ha0 := abs_nonneg ((w - y) / (2 * τ))
    calc
      _ ≤ (2 * (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖)) * gaussDensity τ (w - y) *
          ‖lineFn Λ X w‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hN
        exact mul_le_mul (by linarith only [hle, hs0]) hg hg0 (by positivity)
      _ = _ := by ring
  have hP0 : 0 ≤ P := hPdef ▸ SaddleData.mass_nonneg _ _ _ _ _
  calc
    _ ≤ ((W + 1) / (2 * τ) + ‖horizontalSlope X‖) *
          ∫ w in Ioc (0 : ℝ) W, gaussDensity τ (w + y) * ‖lineFn Λ X w‖ +
        2 * ∫ w in Ioi W, (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) *
          gaussDensity τ (w - y) * ‖lineFn Λ X w‖ := add_le_add h1 h2
    _ ≤ ((W + 1) / (2 * τ) + ‖horizontalSlope X‖) *
          (P * reflectErr K B τ (horizontalSlope X).re y) +
        2 * (P * powerFar K B τ (horizontalSlope X).re) := by
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ hΩ0) (mul_le_mul_of_nonneg_left hfar (by norm_num))
      unfold reflectErr
      exact hrange
    _ = _ := by ring

/-- **The saddle value of the full average.** -/
theorem norm_fullAvg_sub_main_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) (hy : 0 ≤ y)
    (hrefl : ∀ x : ℝ, 0 ≤ x → ‖lineFn Λ X (-x)‖ ≤ ‖lineFn Λ X x‖) :
    ‖fullAvg Λ τ X y - lineF Λ X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))‖ ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ * (8 * τ * (4 * B / η) +
        2 * Real.exp (-(η ^ 2 / (8 * τ))) +
        powerTail K η τ * (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
        powerFar K B τ (horizontalSlope X).re +
        (reflectErr K B τ (horizontalSlope X).re y + powerFar K B τ (horizontalSlope X).re)) := by
  have hτ := h.hτ
  have hint := h.gauss_integrable
  have hsplit : fullAvg Λ τ X y = halfGaussTransform τ (lineFn Λ X) y +
      ∫ w in Ioi (0 : ℝ), (gaussDensity τ (-w - y) : ℂ) * lineFn Λ X (-w) := by
    unfold fullAvg halfGaussTransform
    rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint, compl_Ioi]
    congr 1
    have := integral_comp_neg_Ioi (0 : ℝ)
      (fun w : ℝ => (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w)
    rw [neg_zero] at this
    exact this.symm
  have hleft : ‖∫ w in Ioi (0 : ℝ), (gaussDensity τ (-w - y) : ℂ) * lineFn Λ X (-w)‖ ≤
      ∫ w in Ioi (0 : ℝ), gaussDensity τ (w + y) * ‖lineFn Λ X w‖ := by
    refine norm_integral_le_of_norm_le h.integrable_left.integrableOn
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_))
    have hg : gaussDensity τ (-w - y) = gaussDensity τ (w + y) := by
      rw [show -w - y = -(w + y) by ring, gaussDensity_neg]
    rw [hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussDensity_pos hτ _).le]
    exact mul_le_mul_of_nonneg_left (hrefl w (le_of_lt hw)) (gaussDensity_pos hτ _).le
  have hmain := h.norm_halfGauss_sub_main_le
  have hL := hleft.trans (h.left_mass_le hy)
  rw [hsplit]
  have he : halfGaussTransform τ (lineFn Λ X) y +
        (∫ w in Ioi (0 : ℝ), (gaussDensity τ (-w - y) : ℂ) * lineFn Λ X (-w)) -
        lineF Λ X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) =
      (halfGaussTransform τ (lineFn Λ X) y -
        lineF Λ X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))) +
        ∫ w in Ioi (0 : ℝ), (gaussDensity τ (-w - y) : ℂ) * lineFn Λ X (-w) := by ring
  rw [he, mul_add]
  exact (norm_add_le _ _).trans (add_le_add hmain hL)

/-- **The slope of the full average.** -/
theorem norm_fullMoment_sub_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) (hy : 0 ≤ y)
    (hrefl : ∀ x : ℝ, 0 ≤ x → ‖lineFn Λ X (-x)‖ ≤ ‖lineFn Λ X x‖) :
    ‖fullMoment Λ τ X y - ℓ * fullAvg Λ τ X y‖ ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ * (32 * Real.sqrt τ * (4 * B / η) +
        (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 10) / (2 * τ) * powerTail K η τ *
          (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
        (1 + B) * powerFar K B τ (horizontalSlope X).re +
        (1 + B) * (((2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) / (2 * τ) +
          ‖horizontalSlope X‖) * reflectErr K B τ (horizontalSlope X).re y +
          2 * powerFar K B τ (horizontalSlope X).re)) := by
  have hτ := h.hτ
  have h2τ : 0 < 2 * τ := by positivity
  have hint := h.gauss_integrable
  have hslope := integrable_slope h.model hτ X y
  let m : ℝ → ℂ := fun w => (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn Λ X w -
    ℓ * ((gaussDensity τ (w - y) : ℂ) * lineFn Λ X w)
  have hm : Integrable m := hslope.sub (hint.const_mul ℓ)
  have hsplit : fullMoment Λ τ X y - ℓ * fullAvg Λ τ X y =
      ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn Λ X w) -
        ℓ * halfGaussTransform τ (lineFn Λ X) y) + ∫ w in Ioi (0 : ℝ), m (-w) := by
    have h1 : fullMoment Λ τ X y - ℓ * fullAvg Λ τ X y = ∫ w, m w := by
      unfold fullMoment fullAvg
      rw [← integral_const_mul, ← integral_sub hslope (hint.const_mul ℓ)]
    rw [h1, ← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hm, compl_Ioi]
    congr 1
    · unfold halfGaussTransform
      rw [← integral_const_mul, ← integral_sub hslope.integrableOn (hint.const_mul ℓ).integrableOn]
    · have := integral_comp_neg_Ioi (0 : ℝ) m
      rw [neg_zero] at this
      exact this.symm
  have hweight := (integrable_weight h.model hτ X (-y) ‖horizontalSlope X‖).const_mul (1 + B)
  simp only [sub_neg_eq_add] at hweight
  have hBpos := h.hB_pos
  have hhs1 : 1 ≤ ‖horizontalSlope X‖ := by
    have := Complex.abs_re_le_norm (horizontalSlope X)
    have hab := le_abs_self (horizontalSlope X).re
    linarith only [this, hab, h.hα]
  have hℓn : ‖ℓ‖ ≤ ‖horizontalSlope X‖ + B := by
    have := norm_add_le (ℓ - horizontalSlope X) (horizontalSlope X)
    rw [sub_add_cancel] at this
    linarith only [this, h.hℓ]
  have hleft : ‖∫ w in Ioi (0 : ℝ), m (-w)‖ ≤ (1 + B) * ∫ w in Ioi (0 : ℝ),
      (|(w + y) / (2 * τ)| + ‖horizontalSlope X‖) * gaussDensity τ (w + y) * ‖lineFn Λ X w‖ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le hweight.integrableOn
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_))
    have hg : gaussDensity τ (-w - y) = gaussDensity τ (w + y) := by
      rw [show -w - y = -(w + y) by ring, gaussDensity_neg]
    have hval : m (-w) = ((((-w - y) / (2 * τ) : ℝ) : ℂ) - ℓ) *
        ((gaussDensity τ (w + y) : ℂ) * lineFn Λ X (-w)) := by
      simp only [m]
      rw [hg]
      push_cast
      ring
    rw [hval, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussDensity_pos hτ _).le]
    have hW : ‖(((-w - y) / (2 * τ) : ℝ) : ℂ) - ℓ‖ ≤
        (1 + B) * (|(w + y) / (2 * τ)| + ‖horizontalSlope X‖) := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs,
        show (-w - y) / (2 * τ) = -((w + y) / (2 * τ)) by ring, abs_neg]
      have ha0 := abs_nonneg ((w + y) / (2 * τ))
      nlinarith only [hℓn, hBpos, hhs1, ha0, mul_nonneg hBpos.le ha0]
    have hg0 := (gaussDensity_pos hτ (w + y)).le
    have hle := mul_le_mul_of_nonneg_left (hrefl w (le_of_lt hw)) hg0
    calc
      _ ≤ ((1 + B) * (|(w + y) / (2 * τ)| + ‖horizontalSlope X‖)) *
          (gaussDensity τ (w + y) * ‖lineFn Λ X w‖) :=
        mul_le_mul hW hle (by positivity) (by positivity)
      _ = _ := by ring
  have hmain := h.norm_halfGauss_slope_sub_le
  have hL := hleft.trans (mul_le_mul_of_nonneg_left (h.left_weight_le hy) (by linarith only [hBpos]))
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add hmain hL).trans (le_of_eq ?_))
  ring

end PowerSaddle

end

end GaloisForLFunctions.ZeroConfigurationGeometry
