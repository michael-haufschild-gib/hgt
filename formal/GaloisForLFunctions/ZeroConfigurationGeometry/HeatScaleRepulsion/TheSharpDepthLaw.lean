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
          (∫ w in Ioc (0 : ℝ) W, gaussDensity τ (w + y) * ‖lineFn Λ X w‖) +
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

/-! ## The errors are small -/

/-- The conditions on the slope under which every error of the saddle is small. -/
structure DepthConditions (η α : ℝ) : Prop where
  h8 : 8 ≤ α
  hηα : 64 ≤ η * α
  hB : 3 * η / 2500 * α + powerC₂ η ≤ η * α / 400
  tail1 : 6 / η * Real.exp (powerC₁ η) * (α ^ 3 * Real.exp (-(η ^ 2 / 8 * α))) < 1 / 50
  tail2 : 72 / η * Real.exp (powerC₁ η) * (α ^ 5 * Real.exp (-(η ^ 2 / 8 * α))) < η / 1024
  far : powerC₃ η * Real.exp (2 * powerC₁ η) * (α ^ 2 * Real.exp (-(1 * α))) < η / 1024
  refl1 : Real.exp (powerC₁ η + 1) * (α ^ 0 * Real.exp (-(8 * η * α))) < 1 / 50
  refl2 : 4 * Real.exp (powerC₁ η + 1) * (α ^ 3 * Real.exp (-(8 * η * α))) < η / 1024
  gauss : 2 * (α ^ 0 * Real.exp (-(η ^ 2 / 8 * α))) < 1 / 50

theorem eventually_depthConditions {η : ℝ} (hη : 0 < η) : ∀ᶠ α : ℝ in atTop, DepthConditions η α := by
  have hb : 0 < η ^ 2 / 8 := by positivity
  have hb8 : 0 < 8 * η := by positivity
  have hε : 0 < η / 1024 := by positivity
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_ge_atTop (64 / η),
    eventually_ge_atTop (powerC₂ η / (13 * η / 10000)),
    eventually_const_mul_pow_mul_exp_lt (6 / η * Real.exp (powerC₁ η)) 3 hb
      (by norm_num : (0 : ℝ) < 1 / 50),
    eventually_const_mul_pow_mul_exp_lt (72 / η * Real.exp (powerC₁ η)) 5 hb hε,
    eventually_const_mul_pow_mul_exp_lt (powerC₃ η * Real.exp (2 * powerC₁ η)) 2
      (by norm_num : (0 : ℝ) < 1) hε,
    eventually_const_mul_pow_mul_exp_lt (Real.exp (powerC₁ η + 1)) 0 hb8
      (by norm_num : (0 : ℝ) < 1 / 50),
    eventually_const_mul_pow_mul_exp_lt (4 * Real.exp (powerC₁ η + 1)) 3 hb8 hε,
    eventually_const_mul_pow_mul_exp_lt 2 0 hb (by norm_num : (0 : ℝ) < 1 / 50)]
    with α h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨h1, ?_, ?_, h4, h5, h6, h7, h8, h9⟩
  · rw [div_le_iff₀ hη] at h2
    linarith only [h2]
  · rw [div_le_iff₀ (by positivity)] at h3
    linarith only [h3]

/-- **Every error of the full average is small.** -/
theorem full_errors_le {η τ α B K y A : ℝ} (hη : 0 < η) (hη32 : η ≤ 1 / 32) (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8)
    (hc1 : 16 * η ≤ 2 * τ * α) (hc2 : 2 * τ * α ≤ 1) (hC : DepthConditions η α) (hB5 : 5 ≤ B)
    (hB : B ≤ η * α / 400) (hK0 : 0 ≤ K) (hK : K ≤ Real.exp (η ^ 2 / 1000 * α + powerC₁ η))
    (hy : 5 * η ≤ y) (hsq : Real.sqrt τ ≤ η / 100) (hA0 : 0 ≤ A) (hA : A ≤ α + 1) :
    8 * τ * (4 * B / η) + 2 * Real.exp (-(η ^ 2 / (8 * τ))) +
        powerTail K η τ * (2 * τ * α + α ^ 2 + 1) + powerFar K B τ α +
        (reflectErr K B τ α y + powerFar K B τ α) ≤ 1 / 2 ∧
      4 * τ * (32 * Real.sqrt τ * (4 * B / η) +
        (2 * τ * α + α ^ 2 + 10) / (2 * τ) * powerTail K η τ * (2 * τ * α + α ^ 2 + 1) +
        (1 + B) * powerFar K B τ α +
        (1 + B) * (((2 * τ * α + α ^ 2 + 1) / (2 * τ) + A) * reflectErr K B τ α y +
          2 * powerFar K B τ α)) ≤ η / 32 := by
  have hη8 : η ≤ 1 / 8 := by linarith only [hη32]
  have h1 := hC.h8
  have hα0 : 0 < α := by linarith only [h1]
  have hα1 : 1 ≤ α := by linarith only [h1]
  have hB0 : 0 ≤ B := by linarith only [hB5]
  have htail := powerTail_le hη hη8 hτ hα1 hc1 hc2 hK0 hK
  obtain ⟨hfar1, hfar2⟩ := powerFar_le hη hη8 hτ hτ8 h1 hc1 hc2 hK0 hK hB0 hB
  have hfc : powerC₃ η * Real.exp (2 * powerC₁ η) * (α ^ 2 * Real.exp (-α)) < η / 1024 := by
    have := hC.far
    rwa [one_mul] at this
  have hBF := hfar1.trans_lt hfc
  have hF := hfar2.trans_lt hfc
  obtain ⟨F, hFdef⟩ : ∃ F, F = powerFar K B τ α := ⟨_, rfl⟩
  obtain ⟨Tl, hTldef⟩ : ∃ Tl, Tl = powerTail K η τ := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R, R = reflectErr K B τ α y := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hFdef]
    have := kklRC_nonneg hτ hα0.le
    unfold powerFar
    positivity
  have hTl0 : 0 ≤ Tl := by
    rw [hTldef]
    unfold powerTail
    positivity
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    unfold reflectErr
    positivity
  rw [← hFdef] at hBF hF ⊢
  rw [← hTldef] at htail ⊢
  rw [← hRdef]
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * τ * α + α ^ 2 := ⟨_, rfl⟩
  rw [← hW]
  have hWle : W + 1 ≤ 3 * α ^ 2 := by
    rw [hW]
    nlinarith only [hc2, hα1]
  have hW0 : 0 ≤ W + 1 := by
    rw [hW]
    have : 0 ≤ 2 * τ * α := by positivity
    nlinarith only [this, sq_nonneg α]
  have hWt : W + 10 ≤ 12 * α ^ 2 := by
    rw [hW]
    nlinarith only [hc2, hα1, h1]
  have hexpb := Real.exp_pos (-(η ^ 2 / 8 * α))
  have hc₁ := Real.exp_pos (powerC₁ η)
  -- The tail.
  have hT1 : Tl * (W + 1) < 1 / 50 := by
    have hm := mul_le_mul htail hWle hW0 (by positivity)
    have he : 2 * α / η * Real.exp (powerC₁ η) * Real.exp (-(η ^ 2 / 8 * α)) * (3 * α ^ 2) =
        6 / η * Real.exp (powerC₁ η) * (α ^ 3 * Real.exp (-(η ^ 2 / 8 * α))) := by
      ring
    rw [he] at hm
    exact hm.trans_lt hC.tail1
  have hT2 : (W + 10) * Tl * (W + 1) < η / 1024 := by
    have hW10 : 0 ≤ W + 10 := by linarith only [hW0]
    have hm1 := mul_le_mul hWt htail hTl0 (by positivity)
    have hm2 := mul_le_mul hm1 hWle hW0 (by positivity)
    have he : 12 * α ^ 2 * (2 * α / η * Real.exp (powerC₁ η) * Real.exp (-(η ^ 2 / 8 * α))) * (3 * α ^ 2) =
        72 / η * Real.exp (powerC₁ η) * (α ^ 5 * Real.exp (-(η ^ 2 / 8 * α))) := by
      ring
    rw [he] at hm2
    exact hm2.trans_lt hC.tail2
  -- The window of the saddle.
  have h2τB : 2 * τ * B ≤ η / 400 := by
    have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * τ by positivity)
    nlinarith only [hh, mul_le_mul_of_nonneg_left hc2 hη.le]
  have hwin : 8 * τ * (4 * B / η) ≤ 1 / 25 := by
    have he : 8 * τ * (4 * B / η) = 16 * (2 * τ * B) / η := by ring
    rw [he, div_le_iff₀ hη]
    linarith only [h2τB, hη]
  have hgauss : 2 * Real.exp (-(η ^ 2 / (8 * τ))) < 1 / 50 := by
    have hexp : Real.exp (-(η ^ 2 / (8 * τ))) ≤ Real.exp (-(η ^ 2 / 8 * α)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
      have hsq2 : 0 ≤ η ^ 2 := sq_nonneg η
      nlinarith only [mul_le_mul_of_nonneg_left hc2 hsq2, mul_nonneg hsq2 hτ.le,
        mul_nonneg (mul_nonneg hsq2 hτ.le) hα0.le]
    have h9 := hC.gauss
    simp only [pow_zero, one_mul] at h9
    linarith only [hexp, h9]
  -- The reflection.
  have hR : R ≤ Real.exp (powerC₁ η + 1) * Real.exp (-(8 * η * α)) := by
    have hτB2 : τ * (B + 1 / 8) ^ 2 ≤ η * α := by
      have hle : B + 1 / 8 ≤ 2 * B := by linarith only [hB5]
      have hsq2 := pow_le_pow_left₀ (by linarith only [hB5] : 0 ≤ B + 1 / 8) hle 2
      have hm := mul_le_mul h2τB hB hB0 (by positivity)
      have hηα0 : 0 < η * α := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hsq2 hτ.le, hm, hη8, hηα0, hη]
    have hηsq : η ^ 2 / 1000 * α ≤ η * α := by
      have hηηα := mul_le_mul_of_nonneg_right hη8 (show 0 ≤ η * α by positivity)
      nlinarith only [hηηα, mul_pos hη hα0]
    have hKb : K ≤ Real.exp (η * α + powerC₁ η) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith only [hηsq]))
    have hyα := mul_le_mul_of_nonneg_right hy hα0.le
    rw [hRdef]
    unfold reflectErr
    calc
      _ ≤ Real.exp (η * α + powerC₁ η) * Real.exp 1 *
          Real.exp (-(2 * y * α) + τ * (B + 1 / 8) ^ 2) := by gcongr
      _ = Real.exp (η * α + powerC₁ η + 1 + (-(2 * y * α) + τ * (B + 1 / 8) ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (powerC₁ η + 1 + -(8 * η * α)) :=
        Real.exp_le_exp.mpr (by nlinarith only [hτB2, hyα])
      _ = _ := Real.exp_add _ _
  have hR1 : R < 1 / 50 := by
    have h7 := hC.refl1
    simp only [pow_zero, one_mul] at h7
    exact hR.trans_lt h7
  refine ⟨by linarith only [hwin, hgauss, hT1, hF, hR1, hη32], ?_⟩
  -- The moment errors, against `4τ`.
  have hτ2 : 2 * τ ≤ 1 := by linarith only [hτ8]
  have hs0 := Real.sqrt_nonneg τ
  have ha1 : 4 * τ * (32 * Real.sqrt τ * (4 * B / η)) ≤ 64 / 10000 * η := by
    have he : 4 * τ * (32 * Real.sqrt τ * (4 * B / η)) = (2 * τ * B) * (256 * Real.sqrt τ / η) := by
      field_simp
      ring
    rw [he]
    have hq : 0 ≤ 256 * Real.sqrt τ / η := by positivity
    calc
      _ ≤ η / 400 * (256 * Real.sqrt τ / η) := mul_le_mul_of_nonneg_right h2τB hq
      _ = 64 / 100 * Real.sqrt τ := by
        field_simp
        ring
      _ ≤ _ := by linarith only [hsq]
  have ha2 : 4 * τ * ((W + 10) / (2 * τ) * Tl * (W + 1)) ≤ 2 * (η / 1024) := by
    have he : 4 * τ * ((W + 10) / (2 * τ) * Tl * (W + 1)) = 2 * ((W + 10) * Tl * (W + 1)) := by
      field_simp
      ring
    rw [he]
    linarith only [hT2]
  have hBF0 : 0 ≤ (1 + B) * F := by positivity
  have ha3 : 4 * τ * ((1 + B) * F) ≤ 2 * (η / 1024) := by
    nlinarith only [mul_le_mul_of_nonneg_right hτ2 hBF0, hBF]
  have h1B : 1 + B ≤ α := by
    have hηα : η * α ≤ 1 / 8 * α := mul_le_mul_of_nonneg_right hη8 hα0.le
    linarith only [hB, hηα, h1]
  have ha4 : 4 * τ * ((1 + B) * (((W + 1) / (2 * τ) + A) * R)) ≤ 2 * (η / 1024) := by
    have he : 4 * τ * ((1 + B) * (((W + 1) / (2 * τ) + A) * R)) =
        2 * ((1 + B) * ((W + 1 + 2 * τ * A) * R)) := by
      field_simp
      ring
    rw [he]
    have hτA : 2 * τ * A ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2 * τ by positivity)
      nlinarith only [hm, hc2, hτ2]
    have hsum : W + 1 + 2 * τ * A ≤ 4 * α ^ 2 := by
      have hα2 : 2 ≤ α ^ 2 := by nlinarith only [hα1, h1]
      linarith only [hWle, hτA, hα2]
    have hsum0 : 0 ≤ W + 1 + 2 * τ * A := by
      have : 0 ≤ 2 * τ * A := by positivity
      linarith only [hW0, this]
    have hb1 : (W + 1 + 2 * τ * A) * R ≤ 4 * α ^ 2 * (Real.exp (powerC₁ η + 1) * Real.exp (-(8 * η * α))) :=
      mul_le_mul hsum hR hR0 (by positivity)
    have hb2 : (1 + B) * ((W + 1 + 2 * τ * A) * R) ≤
        α * (4 * α ^ 2 * (Real.exp (powerC₁ η + 1) * Real.exp (-(8 * η * α)))) :=
      mul_le_mul h1B hb1 (by positivity) hα0.le
    have he2 : α * (4 * α ^ 2 * (Real.exp (powerC₁ η + 1) * Real.exp (-(8 * η * α)))) =
        4 * Real.exp (powerC₁ η + 1) * (α ^ 3 * Real.exp (-(8 * η * α))) := by ring
    rw [he2] at hb2
    linarith only [hb2, hC.refl2]
  have ha5 : 4 * τ * ((1 + B) * (2 * F)) ≤ 4 * (η / 1024) := by
    have he : 4 * τ * ((1 + B) * (2 * F)) = 2 * (2 * τ * 2 * ((1 + B) * F)) := by ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right hτ2 hBF0, hBF]
  have hexpand : 4 * τ * (32 * Real.sqrt τ * (4 * B / η) +
        (W + 10) / (2 * τ) * Tl * (W + 1) + (1 + B) * F +
        (1 + B) * (((W + 1) / (2 * τ) + A) * R + 2 * F)) =
      4 * τ * (32 * Real.sqrt τ * (4 * B / η)) + 4 * τ * ((W + 10) / (2 * τ) * Tl * (W + 1)) +
        4 * τ * ((1 + B) * F) + 4 * τ * ((1 + B) * (((W + 1) / (2 * τ) + A) * R)) +
        4 * τ * ((1 + B) * (2 * F)) := by ring
  rw [hexpand]
  linarith only [ha1, ha2, ha3, ha4, ha5, hη]

/-! ## The zero -/

namespace IsolatedZero

variable {d η E T t : ℝ}

/-- **The exact identity.** `c H_τ = (½ + iz − ρ) 𝓖 + 2τ D`. -/
theorem heat_identity (h : IsolatedZero d η E T t) (hT : 8 ≤ T) {τ : ℝ} (hτ : 0 < τ) (X y : ℝ)
    (h1 : Integrable fun w : ℝ => (gaussDensity τ (w - y) : ℂ) * lineFn (quotXi d t) X w)
    (h2 : Integrable fun w : ℝ => (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) *
      lineFn (quotXi d t) X w) :
    ((3 / 2 - d : ℝ) : ℂ) * riemannHeat τ ((X : ℂ) - I * y) =
      (1 / 2 + (y : ℂ) + I * X - depthPoint d t) * fullAvg (quotXi d t) τ X y +
        2 * (τ : ℂ) * fullMoment (quotXi d t) τ X y := by
  rw [riemannHeat_eq_fullAvg_xi hτ]
  unfold fullAvg fullMoment
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (h1.const_mul _) (h2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  have hx : lineFn xi X w = (1 / 2 + (w : ℂ) + I * X - depthPoint d t) *
      dslope xi (depthPoint d t) (1 / 2 + (w : ℂ) + I * X) := (h.sub_mul_dslope hT _).symm
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  simp only
  rw [hx]
  unfold lineFn quotXi
  push_cast
  field_simp
  ring

/-- The quotient is entire below the growth horizon. -/
theorem differentiable_gaussAverage_quotXi (h : IsolatedZero d η E T t) (hT : 8 ≤ T) {τ : ℝ} (hτ : 0 < τ)
    (hτS : 8 * xiApproxGrowth * τ < 1) : Differentiable ℂ (gaussAverage (quotXi d t) τ) := by
  obtain ⟨M, hM0, hM⟩ := h.exists_norm_dslope_le hT
  have hc1 := h.three_halves_sub_pos
  have hS := xiApproxGrowth_nonneg
  refine differentiable_gaussAverage (differentiable_quotXi d t) hτ
    (C := (3 / 2 - d) * (M + ‖XiC 0‖)) (S := xiApproxGrowth) (by
      have := norm_nonneg (XiC 0)
      have hc : 0 ≤ 3 / 2 - d := by linarith only [hc1]
      positivity) hS hτS fun z => ?_
  unfold quotXi
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hc1]), mul_assoc]
  refine mul_le_mul_of_nonneg_left ((hM _).trans ?_) (by linarith only [hc1])
  rw [← riemannHeat_zero]
  have hb := norm_riemannHeat_zero_le_exp_sq z
  have he : 1 ≤ Real.exp (xiApproxGrowth * ‖z‖ ^ 2) := Real.one_le_exp (by positivity)
  rw [add_mul]
  nlinarith only [hb, he, hM0]

end IsolatedZero

/-- **The zero of the flow near an isolated deep zero.** -/
theorem eventually_exists_zero_near {η : ℝ} (hη : 0 < η) (hη32 : η ≤ 1 / 32) :
    ∀ᶠ T : ℝ in atTop, ∀ d t : ℝ, IsolatedZero d η (powerLevel η / 2) T t → 30 * η ≤ d →
      ∀ τ : ℝ, 0 < τ → τ * Real.log (t / (2 * Real.pi)) = d - 6 * η →
      ∃ z : ℂ, riemannHeat τ z = 0 ∧ z.im ≠ 0 ∧ |z.re - t| ≤ η := by
  have hη8 : η ≤ 1 / 8 := by linarith only [hη32]
  obtain ⟨S, hSdef⟩ : ∃ S, S = xiApproxGrowth := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hSdef ▸ xiApproxGrowth_nonneg
  have hcond : ∀ᶠ α : ℝ in atTop, DepthConditions η α ∧ 5000 / η ^ 2 ≤ α ∧ 2 * S + 1 ≤ α := by
    filter_upwards [eventually_depthConditions hη, eventually_ge_atTop (5000 / η ^ 2),
      eventually_ge_atTop (2 * S + 1)] with α h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp hcond
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (tendsto_horizontalSlope_re.eventually_ge_atTop A)
  have hE : 0 ≤ powerLevel η := by
    unfold powerLevel
    positivity
  have hE0 : 0 < powerLevel η / 2 := by
    unfold powerLevel
    positivity
  filter_upwards [eventually_ge_atTop (max X₀ 1000 + 2), eventually_ge_atTop (8 : ℝ),
    (tendsto_rpow_atTop hE0).eventually_ge_atTop (3 / η)] with T hTbig hT hA3
  intro d t h hd τ hτ hτL
  have hm := h.mem
  have hη2 : η ≤ 1 / 2 := by linarith only [hη32]
  obtain ⟨B, hBdef⟩ : ∃ B, B = powerSlopeError (powerLevel η) η T := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = powerRatio (powerLevel η) η T := ⟨_, rfl⟩
  have hmodel : LineModel (quotXi d t) (d - 13 * η) η B K t := by
    rw [hBdef, hKdef]
    exact h.lineModel hη hη2 hT hE hA3
  -- The parameters at every height near `t`.
  have hparam : ∀ X : ℝ, |X - t| ≤ 1 → 1000 ≤ X ∧ DepthConditions η (horizontalSlope X).re ∧
      5000 / η ^ 2 ≤ (horizontalSlope X).re ∧ 2 * S + 1 ≤ (horizontalSlope X).re ∧
      B ≤ η * (horizontalSlope X).re / 400 ∧ 5 ≤ B ∧
      K ≤ Real.exp (η ^ 2 / 1000 * (horizontalSlope X).re + powerC₁ η) := by
    intro X hXt
    have hXt' := abs_le.mp hXt
    have hTX : T - 1 ≤ X := by linarith only [hm.1, hXt'.1]
    have hXm : max X₀ 1000 ≤ X := by linarith only [hTbig, hTX]
    have hX : 1000 ≤ X := (le_max_right _ _).trans hXm
    have hX0 : 0 < X := by linarith only [hX]
    obtain ⟨α, hαdef⟩ : ∃ α, α = (horizontalSlope X).re := ⟨_, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hA α (hαdef ▸ hX₀ X ((le_max_left _ _).trans hXm))
    have hα0 : 0 < α := by linarith only [h1.h8]
    have hL : Real.log T ≤ 2 * α + 15 := by
      have hT0 : 0 < T := by linarith only [hT]
      have hmono := Real.log_le_log hT0 (show T ≤ 2 * X by linarith only [hTX, hX])
      rw [Real.log_mul (by norm_num) hX0.ne'] at hmono
      have hh := height_eq hX0
      rw [← hαdef] at hh
      have hlogX : Real.log X = Real.log (2 * Real.pi) + 2 * α := by
        rw [hh, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith only [this]
      have hlogπ : Real.log (2 * Real.pi) ≤ 7 :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith only [Real.pi_lt_four])
      linarith only [hmono, hlogX, hlog2, hlogπ]
    have hBle := powerSlopeError_le hη hη8 hL
    have hKle := powerRatio_le hη hη8 hT hα0.le hL
    rw [← hBdef] at hBle
    rw [← hKdef] at hKle
    have hB5 : 5 ≤ B := by
      rw [hBdef]
      unfold powerSlopeError
      have hlog := Real.log_nonneg (by linarith only [hT] : (1 : ℝ) ≤ T)
      have hq : 0 ≤ 24 * (powerLevel η * Real.log T + 9) / η ^ 2 := by positivity
      linarith only [hq]
    subst hαdef
    exact ⟨hX, h1, h2, h3, by linarith only [hBle, h1.hB], hB5, hKle⟩
  -- The parameters at the height of the zero.
  have htt : |t - t| ≤ 1 := by simp
  obtain ⟨ht1000, hC₀, hα₀2, hα₀3, _, hB5, _⟩ := hparam t htt
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, α₀ = (horizontalSlope t).re := ⟨_, rfl⟩
  rw [← hα₀] at hC₀ hα₀2 hα₀3
  have hα₀8 := hC₀.h8
  have hα₀0 : 0 < α₀ := by linarith only [hα₀8]
  have hc₀ : 2 * τ * α₀ = d - 6 * η := by
    rw [← hτL, hα₀, horizontalSlope_re]
    ring
  have hd2 := h.hd2
  have hc₀2 : 2 * τ * α₀ ≤ 1 / 2 := by linarith only [hc₀, hd2, hη]
  have h2τ : 2 * τ ≤ η / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hC₀.hηα (show 0 ≤ 2 * τ by positivity)
    have h2 := mul_le_mul_of_nonneg_left hc₀2 hη.le
    nlinarith only [h1, h2]
  have hτα : τ * α₀ ≤ 1 / 4 := by linarith only [hc₀2]
  have hτsq : τ ≤ (η / 100) ^ 2 := by
    have hη2pos : 0 < η ^ 2 := by positivity
    rw [div_le_iff₀ hη2pos] at hα₀2
    have hm1 := mul_le_mul_of_nonneg_left hα₀2 hτ.le
    have : τ * 5000 ≤ η ^ 2 * (τ * α₀) := by nlinarith only [hm1]
    nlinarith only [this, mul_le_mul_of_nonneg_left hτα hη2pos.le]
  have hsq : Real.sqrt τ ≤ η / 100 := (Real.sqrt_le_left (by positivity)).mpr hτsq
  have hτS : 8 * xiApproxGrowth * τ < 1 := by
    rw [← hSdef]
    have h1 := mul_le_mul_of_nonneg_left hα₀3 hτ.le
    nlinarith only [h1, hτα, hτ, hS0]
  have hτ8 : τ ≤ 1 / 8 := by linarith only [h2τ, hη32]
  -- The disc.
  let Λ := quotXi d t
  have hc1 := h.three_halves_sub_pos
  have hcne : (((3 / 2 - d : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith only [hc1]))
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, z₀ = -I * (depthPoint d t - 2 * (τ : ℂ) * horizontalSlope t - 1 / 2) := ⟨_, rfl⟩
  have hz₀re : z₀.re = t - 2 * τ * (Real.pi / 4) := by
    rw [hz₀]
    have hi := depthPoint_im d t
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im, Complex.sub_im,
      Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      horizontalSlope_im, Complex.sub_re, Complex.div_ofNat_im, Complex.one_im, hi]
    ring
  have hz₀im : z₀.im = -(6 * η) := by
    rw [hz₀]
    have hi := depthPoint_re d t
    simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im, Complex.sub_re,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, Complex.div_ofNat_re, Complex.one_re, hi, ← hα₀]
    have := hc₀
    linarith only [this]
  have hπ := Real.pi_lt_four
  have hπ0 := Real.pi_pos
  have hτπ : 2 * τ * (Real.pi / 4) ≤ η / 128 := by
    have : 2 * τ * (Real.pi / 4) ≤ 2 * τ * 1 :=
      mul_le_mul_of_nonneg_left (by linarith only [hπ]) (by positivity)
    linarith only [this, h2τ]
  have hτπ0 : 0 ≤ 2 * τ * (Real.pi / 4) := by positivity
  let ψ : ℂ → ℂ := fun z => z + I * (((3 / 2 - d : ℝ) : ℂ) * riemannHeat τ z) / gaussAverage Λ τ z
  -- The estimates at one point of the disc.
  have hpoint : ∀ z ∈ ball z₀ (η / 4), gaussAverage Λ τ z ≠ 0 ∧ ‖ψ z - z₀‖ ≤ η / 8 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt hz)
    have him := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt hz)
    rw [Complex.sub_re, hz₀re] at hre
    rw [Complex.sub_im, hz₀im] at him
    obtain ⟨X, hXdef⟩ : ∃ X, X = z.re := ⟨_, rfl⟩
    obtain ⟨y, hydef⟩ : ∃ y, y = -z.im := ⟨_, rfl⟩
    rw [← hXdef] at hre
    have hzrep : z = (X : ℂ) - I * y := by
      apply Complex.ext
      · simp [hXdef]
      · simp [hydef]
    have hy1 : 5 * η ≤ y := by rw [hydef]; linarith only [him.2, hη]
    have hy1' : 23 / 4 * η ≤ y := by rw [hydef]; linarith only [him.2]
    have hy2 : y ≤ 13 / 2 * η := by rw [hydef]; linarith only [him.1, hη]
    have hXt : |X - t| ≤ η / 2 := abs_le.mpr ⟨by linarith only [hre.1, hτπ, hη],
      by linarith only [hre.2, hτπ0, hη]⟩
    have hXt1 : |X - t| ≤ 1 := hXt.trans (by linarith only [hη32])
    obtain ⟨hX, hC, _, _, hB, _, hK⟩ := hparam X hXt1
    obtain ⟨α, hαdef⟩ : ∃ α, α = (horizontalSlope X).re := ⟨_, rfl⟩
    rw [← hαdef] at hC hB hK
    have hα8 := hC.h8
    have hα0 : 0 < α := by linarith only [hα8]
    have hslopeD : ‖horizontalSlope X - horizontalSlope t‖ ≤ 1 := by
      rw [norm_sub_rev]
      exact norm_horizontalSlope_sub_le (X := X) (Y := t) (by linarith only [hX])
        (by rw [abs_sub_comm]; exact hXt1) |> fun h => by rwa [norm_sub_rev] at h ⊢
    have hαD : |α - α₀| ≤ 1 := by
      have := Complex.abs_re_le_norm (horizontalSlope X - horizontalSlope t)
      rw [Complex.sub_re, ← hαdef, ← hα₀] at this
      exact this.trans hslopeD
    have hαD' := abs_le.mp hαD
    have hτα1 : 2 * τ * α ≤ 2 * τ * α₀ + 2 * τ := by
      have := mul_le_mul_of_nonneg_left hαD'.2 (show 0 ≤ 2 * τ by positivity)
      linarith only [this]
    have hτα2 : 2 * τ * α₀ - 2 * τ ≤ 2 * τ * α := by
      have := mul_le_mul_of_nonneg_left hαD'.1 (show 0 ≤ 2 * τ by positivity)
      linarith only [this]
    have hc1' : 16 * η ≤ 2 * τ * α := by linarith only [hτα2, hc₀, h2τ, hd, hη]
    have hc2' : 2 * τ * α ≤ 1 := by linarith only [hτα1, hc₀2, h2τ, hη32]
    have hyc : d - 13 * η + 12 * η ≤ y + 2 * τ * α := by linarith only [hτα2, hc₀, hy1', h2τ, hη]
    have hy2' : y ≤ 1 / 2 := by linarith only [hy2, hη32]
    have hy0 : 0 ≤ y := by linarith only [hy1, hη]
    obtain ⟨a, δ, ℓ, hs, _⟩ := exists_powerSaddle (y := y) hmodel hη hη8 hX (hαdef ▸ hα8)
      (hαdef ▸ (by nlinarith only [hC.hηα])) hXt hτ hτ8 (hαdef ▸ hc1') (hαdef ▸ hc2')
      (by linarith only [hy0]) hy2' (hαdef ▸ hyc) (hαdef ▸ hB)
    have hrefl : ∀ x : ℝ, 0 ≤ x → ‖lineFn (quotXi d t) X (-x)‖ ≤ ‖lineFn (quotXi d t) X x‖ :=
      fun x hx => h.norm_lineFn_neg_le hη hT X hx
    have hP := hs.mass_pos
    obtain ⟨hE0', hE1'⟩ := full_errors_le (A := ‖horizontalSlope X‖) hη hη32 hτ hτ8 hc1' hc2' hC hB5
      (hB) hmodel.hK.le hK hy1 hsq (norm_nonneg _) (by
        rw [hαdef]
        exact _root_.RHTower.DeBruijn.norm_horizontalSlope_le (hαdef ▸ hα0.le))
    have h1 := hs.norm_fullAvg_sub_main_le hy0 hrefl
    have h2 := hs.norm_fullMoment_sub_le hy0 hrefl
    rw [← hαdef] at h1 h2
    obtain ⟨P, hPdef⟩ : ∃ P, P = SaddleData.mass (lineF (quotXi d t) X) τ a δ ℓ := ⟨_, rfl⟩
    rw [← hPdef] at hP h1 h2
    have hM := SaddleData.norm_main (lineF (quotXi d t) X) τ a δ ℓ
    rw [← hPdef] at hM
    have hb0 := h1.trans (mul_le_mul_of_nonneg_left hE0' hP.le)
    obtain ⟨G, hGdef⟩ : ∃ G, G = fullAvg (quotXi d t) τ X y := ⟨_, rfl⟩
    obtain ⟨D, hDdef⟩ : ∃ D, D = fullMoment (quotXi d t) τ X y := ⟨_, rfl⟩
    rw [← hGdef] at hb0 h2
    rw [← hDdef] at h2
    have hGlow : P / 2 ≤ ‖G‖ := by
      have hn := norm_sub_norm_le (lineF (quotXi d t) X ((a : ℂ) + (δ : ℂ) * I) *
        Complex.exp (-((τ : ℂ) * ℓ ^ 2))) G
      rw [norm_sub_rev, hM] at hn
      linarith only [hn, hb0]
    have hGpos : 0 < ‖G‖ := by linarith only [hGlow, hP]
    have hGne : G ≠ 0 := norm_pos_iff.mp hGpos
    have hgavg : gaussAverage Λ τ z = G := by
      rw [hzrep, hGdef]
      exact gaussAverage_eq_fullAvg _ τ X y
    have hid := h.heat_identity hT hτ X y hs.gauss_integrable (PowerSaddle.integrable_slope hmodel hτ X y)
    rw [← hGdef, ← hDdef, ← hzrep] at hid
    refine ⟨by rw [hgavg]; exact hGne, ?_⟩
    have hIz : (1 / 2 + (y : ℂ) + I * X : ℂ) = 1 / 2 + I * z := by
      rw [hzrep]
      linear_combination (y : ℂ) * Complex.I_sq
    rw [hIz] at hid
    have hψ : ψ z - z₀ = 2 * (τ : ℂ) * I * (D / G - horizontalSlope t) := by
      have hdiv : I * ((1 / 2 + I * z - depthPoint d t) * G + 2 * (τ : ℂ) * D) / G =
          I * (1 / 2 + I * z - depthPoint d t) + 2 * (τ : ℂ) * I * (D / G) := by
        field_simp
      simp only [ψ]
      rw [hgavg, hid, hz₀, hdiv]
      linear_combination z * Complex.I_sq
    rw [hψ, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg hτ.le]
    obtain ⟨Er, hErdef⟩ : ∃ Er, Er = 32 * Real.sqrt τ * (4 * B / η) +
        (2 * τ * α + α ^ 2 + 10) / (2 * τ) * powerTail K η τ * (2 * τ * α + α ^ 2 + 1) +
        (1 + B) * powerFar K B τ α +
        (1 + B) * (((2 * τ * α + α ^ 2 + 1) / (2 * τ) + ‖horizontalSlope X‖) *
          reflectErr K B τ α y + 2 * powerFar K B τ α) := ⟨_, rfl⟩
    rw [← hErdef] at h2 hE1'
    have hquot : ‖D / G - ℓ‖ ≤ 2 * Er := by
      have he : D / G - ℓ = (D - ℓ * G) / G := by
        field_simp
      rw [he, norm_div, div_le_iff₀ hGpos]
      have hEr0 : 0 ≤ Er := by
        have hP2 := (norm_nonneg _).trans h2
        by_contra hneg
        push Not at hneg
        nlinarith only [hP2, hneg, hP]
      nlinarith only [h2, mul_le_mul_of_nonneg_left hGlow hEr0]
    have hℓX : ‖ℓ - horizontalSlope X‖ ≤ B := hs.hℓ
    have htri : ‖D / G - horizontalSlope t‖ ≤ 2 * Er + B + 1 := by
      have he : D / G - horizontalSlope t = (D / G - ℓ) + (ℓ - horizontalSlope X) +
          (horizontalSlope X - horizontalSlope t) := by ring
      rw [he]
      have := norm_add₃_le (a := D / G - ℓ) (b := ℓ - horizontalSlope X)
        (c := horizontalSlope X - horizontalSlope t)
      linarith only [this, hquot, hℓX, hslopeD]
    have h2τB : 2 * τ * B ≤ η / 400 := hs.hτB
    have hmul := mul_le_mul_of_nonneg_left htri (show 0 ≤ 2 * τ by positivity)
    have hexp : 2 * τ * (2 * Er + B + 1) = 4 * τ * Er + 2 * τ * B + 2 * τ := by ring
    rw [hexp] at hmul
    linarith only [hmul, hE1', h2τB, h2τ, hη]
  have hdiff : DifferentiableOn ℂ ψ (ball z₀ (η / 4)) := by
    intro z hz
    have hgd := (h.differentiable_gaussAverage_quotXi hT hτ hτS) z
    have hHd := differentiable_riemannHeat hτ.le z
    exact (differentiableAt_id.add (((differentiableAt_const _).mul
      ((differentiableAt_const _).mul hHd)).div hgd (hpoint z hz).1)).differentiableWithinAt
  obtain ⟨p, hp, hfix, _⟩ := HTGeometry.DiscFixedPoint.exists_unique_fixedPoint (ψ := ψ) (c := z₀)
    (R := η / 4) (θ := 1 / 2) (by positivity) (by norm_num) (by norm_num) hdiff
    (fun z hz => by
      rw [mem_closedBall, dist_eq_norm]
      have := (hpoint z hz).2
      linarith only [this])
  rw [mem_closedBall, dist_eq_norm] at hp
  have hpb : p ∈ ball z₀ (η / 4) := by
    rw [mem_ball, dist_eq_norm]
    linarith only [hp, hη]
  have hzero : riemannHeat τ p = 0 := by
    have hz : I * (((3 / 2 - d : ℝ) : ℂ) * riemannHeat τ p) / gaussAverage Λ τ p = 0 := by
      have := hfix
      simp only [ψ] at this
      exact add_eq_left.mp this
    rcases div_eq_zero_iff.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact absurd hz Complex.I_ne_zero
      · exact (mul_eq_zero.mp hz).resolve_left hcne
    · exact absurd hz (hpoint p hpb).1
  have hpre := abs_le.mp ((Complex.abs_re_le_norm _).trans hp)
  have hpim := abs_le.mp ((Complex.abs_im_le_norm _).trans hp)
  rw [Complex.sub_re, hz₀re] at hpre
  rw [Complex.sub_im, hz₀im] at hpim
  refine ⟨p, hzero, ?_, abs_le.mpr ⟨by linarith only [hpre.1, hτπ, hη], by linarith only [hpre.2, hτπ0, hη]⟩⟩
  have : p.im < 0 := by linarith only [hpim.2, hη]
  exact this.ne

/-- A nonreal zero of `H_τ` over the window forces `Λ_X ≥ τ`. -/
theorem le_localNewmanConstant_of_nonreal_zero {τ X : ℝ} {z : ℂ} (hz : riemannHeat τ z = 0) (him : z.im ≠ 0)
    (hw : |z.re - X| ≤ 1) : τ ≤ localNewmanConstant X := by
  refine le_csInf (localRealTimes_nonempty X) fun s hs => ?_
  by_contra hlt
  exact him (hs.2 τ (not_le.mp hlt).le z hz hw)

/-- **The lower bound of the sharp depth law.** Near an isolated zero of depth `d`, `Λ_X log(t/2π) ≥ d − 6η`. -/
theorem eventually_le_localNewmanConstant_of_isolatedZero {η : ℝ} (hη : 0 < η) (hη32 : η ≤ 1 / 32) :
    ∀ᶠ T : ℝ in atTop, ∀ d t : ℝ, IsolatedZero d η (powerLevel η / 2) T t → 30 * η ≤ d →
      ∀ X : ℝ, |X - t| ≤ 1 / 2 →
        (d - 6 * η) / Real.log (t / (2 * Real.pi)) ≤ localNewmanConstant X := by
  filter_upwards [eventually_exists_zero_near hη hη32,
    eventually_ge_atTop (2 * Real.pi * Real.exp 1)] with T hzero hT
  intro d t h hd X hX
  have hπ : 0 < 2 * Real.pi := by positivity
  have hratio : Real.exp 1 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ hπ]
    linarith only [hT, h.mem.1]
  have hL : 1 ≤ Real.log (t / (2 * Real.pi)) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hratio
    simpa only [Real.log_exp] using hh
  have hL0 : 0 < Real.log (t / (2 * Real.pi)) := by linarith only [hL]
  have hτ : 0 < (d - 6 * η) / Real.log (t / (2 * Real.pi)) :=
    div_pos (by linarith only [hd, hη]) hL0
  obtain ⟨z, hz, him, hre⟩ := hzero d t h hd _ hτ (div_mul_cancel₀ _ hL0.ne')
  refine le_localNewmanConstant_of_nonreal_zero hz him ?_
  have h1 := abs_le.mp hre
  have h2 := abs_le.mp hX
  exact abs_le.mpr ⟨by linarith only [h1.1, h2.2, hη32], by linarith only [h1.2, h2.1, hη32]⟩

/-- **The sharp depth law.** On a window of depth `d` around an isolated zero of depth `d`, outside crowds,
`d − 7η ≤ Λ_X log(X/2π) ≤ d + 17η`. -/
theorem localNewman_scaled_mem_Icc {η : ℝ} (hη : 0 < η) (hη32 : η ≤ 1 / 32) :
    ∀ᶠ T : ℝ in atTop, ∀ d t X : ℝ, IsolatedZero d η (powerLevel η / 2) T t → 30 * η ≤ d →
      |X - t| ≤ 1 / 2 → X ∈ Icc T (2 * T) → depthWindow d η T X →
        d - 7 * η ≤ localNewmanConstant X * Real.log (X / (2 * Real.pi)) ∧
          localNewmanConstant X * Real.log (X / (2 * Real.pi)) ≤ d + 17 * η := by
  filter_upwards [eventually_le_localNewmanConstant_of_isolatedZero hη hη32,
    eventually_localNewmanConstant_le_of_depthWindow hη (by linarith only [hη32]),
    eventually_ge_atTop (2 * Real.pi * Real.exp 1 + 2), eventually_ge_atTop (1 / η + 2)] with
    T hlow hup hT hTη
  intro d t X h hd hXt hX hwin
  have hπ : 0 < 2 * Real.pi := by positivity
  have hd2 := h.hd2
  have hd0 : 0 ≤ d := by linarith only [hd, hη]
  have he1 := Real.exp_pos (1 : ℝ)
  have hT3 : 3 ≤ T := by
    have := mul_pos hπ he1
    nlinarith only [hT, Real.pi_gt_three, Real.add_one_le_exp (1 : ℝ)]
  have hX1 := hX.1
  have hXt' := abs_le.mp hXt
  have ht1 := h.mem.1
  have hratio (Y : ℝ) (hY : T - 1 ≤ Y) : 1 ≤ Real.log (Y / (2 * Real.pi)) := by
    have hr : Real.exp 1 ≤ Y / (2 * Real.pi) := by
      rw [le_div_iff₀ hπ]
      linarith only [hT, hY]
    have hh := Real.log_le_log he1 hr
    simpa only [Real.log_exp] using hh
  have hLX := hratio X (by linarith only [hX1])
  have hLt := hratio t (by linarith only [ht1])
  have hLm := hratio (X - 1) (by linarith only [hX1])
  have hlowb := hlow d t h hd X hXt
  have hupb := hup d X hX hwin hd0
  have hη1T : 1 / T ≤ η := by
    have hTpos : 0 < T := by linarith only [hT3]
    rw [div_le_iff₀ hTpos]
    have hηT : 1 / η ≤ T := by linarith only [hTη]
    rw [div_le_iff₀ hη] at hηT
    linarith only [hηT]
  constructor
  · -- The logarithms at `X` and `t` differ by at most `1/T`.
    have hdiff : Real.log (t / (2 * Real.pi)) - Real.log (X / (2 * Real.pi)) ≤ 1 / T := by
      have hXp : 0 < X := by linarith only [hX1, hT3]
      have htp : 0 < t := by linarith only [ht1, hT3]
      have heq : Real.log (t / (2 * Real.pi)) - Real.log (X / (2 * Real.pi)) = Real.log (t / X) := by
        rw [Real.log_div htp.ne' hπ.ne', Real.log_div hXp.ne' hπ.ne', Real.log_div htp.ne' hXp.ne']
        ring
      rw [heq]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      have hq : t / X - 1 = (t - X) / X := by
        field_simp
      rw [hq]
      have hTpos : 0 < T := by linarith only [hT3]
      calc
        _ ≤ 1 / X := div_le_div_of_nonneg_right (by linarith only [hXt'.1]) hXp.le
        _ ≤ 1 / T := one_div_le_one_div_of_le hTpos hX1
    have hLt0 : 0 < Real.log (t / (2 * Real.pi)) := by linarith only [hLt]
    have hLX0 : 0 < Real.log (X / (2 * Real.pi)) := by linarith only [hLX]
    have hm := mul_le_mul_of_nonneg_right hlowb hLX0.le
    refine le_trans ?_ hm
    rw [div_mul_eq_mul_div, le_div_iff₀ hLt0]
    have hdη : 0 ≤ d - 6 * η := by linarith only [hd, hη]
    have hdη1 : d - 6 * η ≤ 1 := by linarith only [hd2, hη]
    have hstep := mul_le_mul_of_nonneg_left hdiff hdη
    have hLtm := mul_le_mul_of_nonneg_right (show (d - 7 * η) ≤ d - 6 * η by linarith only [hη]) hLt0.le
    nlinarith only [hstep, hη1T, hdη1, hη, hLt, hdη,
      mul_le_mul_of_nonneg_left hη1T hdη, mul_nonneg hη.le (sub_nonneg.mpr hLt)]
  · have hdiff : Real.log (X / (2 * Real.pi)) - Real.log ((X - 1) / (2 * Real.pi)) ≤ 1 / (T - 1) := by
      have hXp : 0 < X := by linarith only [hX1, hT3]
      have hX1p : 0 < X - 1 := by linarith only [hX1, hT3]
      have heq : Real.log (X / (2 * Real.pi)) - Real.log ((X - 1) / (2 * Real.pi)) =
          Real.log (X / (X - 1)) := by
        rw [Real.log_div hXp.ne' hπ.ne', Real.log_div hX1p.ne' hπ.ne', Real.log_div hXp.ne' hX1p.ne']
        ring
      rw [heq]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      have hq : X / (X - 1) - 1 = 1 / (X - 1) := by
        field_simp
        ring
      rw [hq]
      exact one_div_le_one_div_of_le (by linarith only [hT3]) (by linarith only [hX1])
    have hη1T1 : 1 / (T - 1) ≤ η := by
      have hTpos : 0 < T - 1 := by linarith only [hT3]
      rw [div_le_iff₀ hTpos]
      have hηT : 1 / η + 1 ≤ T := by linarith only [hTη]
      have hηT' : 1 / η ≤ T - 1 := by linarith only [hηT]
      rw [div_le_iff₀ hη] at hηT'
      linarith only [hηT']
    have hLm0 : 0 < Real.log ((X - 1) / (2 * Real.pi)) := by linarith only [hLm]
    have hLX0 : 0 < Real.log (X / (2 * Real.pi)) := by linarith only [hLX]
    have hm := mul_le_mul_of_nonneg_right hupb hLX0.le
    refine hm.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hLm0]
    have hA : 0 ≤ d + 16 * η := by linarith only [hd0, hη]
    have hA1 : d + 16 * η ≤ 1 := by linarith only [hd2, hη32]
    have hstep := mul_le_mul_of_nonneg_left (hdiff.trans hη1T1) hA
    nlinarith only [hstep, hA1, hη, hLm, hA, mul_nonneg hη.le (sub_nonneg.mpr hLm),
      mul_le_mul_of_nonneg_right hA1 hη.le]

end

end GaloisForLFunctions.ZeroConfigurationGeometry
