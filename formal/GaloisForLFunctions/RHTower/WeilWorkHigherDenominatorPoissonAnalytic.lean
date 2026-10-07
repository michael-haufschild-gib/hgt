import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonSmooth
import GaloisForLFunctions.RHTower.MaassConverseAutomorphy

/-!
# Horizontal real analyticity of the actual polynomial Poisson modes

Complexifying the horizontal coordinate keeps the projective denominator in
the right half-plane on a strip. Compact parameters provide the uniform
majorants for complex differentiation under the fixed weighted integral.
-/

noncomputable section

open Complex Set Filter MeasureTheory Metric Polynomial

namespace RHTower.WeilHigherDenominator

/-- A complex neighborhood of every real horizontal coordinate at height `y`. -/
def poissonHorizontalStrip (y : ℝ) : Set ℂ := {w | |w.im| < y / 2}

private lemma isOpen_poissonHorizontalStrip (y : ℝ) : IsOpen (poissonHorizontalStrip y) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- The polynomial denominator of the holomorphic horizontal extension. -/
def horizontalPoissonDenom (y : ℝ) (w c : ℂ) : ℂ :=
  (w * (c.im : ℂ) + (c.re : ℂ)) ^ 2 + ((y : ℂ) * (c.im : ℂ)) ^ 2

/-- The branch is safe on the whole strip, including projective endpoints. -/
theorem horizontalPoissonDenom_re_pos {y : ℝ} (hy : 0 < y) {w c : ℂ}
    (hw : w ∈ poissonHorizontalStrip y) (hc : c ≠ 0) :
    0 < (horizontalPoissonDenom y w c).re := by
  have hq : (horizontalPoissonDenom y w c).re =
      (w.re * c.im + c.re) ^ 2 + (y ^ 2 - w.im ^ 2) * c.im ^ 2 := by
    simp only [horizontalPoissonDenom, pow_two, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
    ring
  rw [hq]
  by_cases ha : c.im = 0
  · have hb : c.re ≠ 0 := by
      intro hb
      exact hc (Complex.ext (by simpa using hb) (by simpa using ha))
    simpa [ha] using sq_pos_of_ne_zero hb
  · have hw' : |w.im| < y := lt_trans hw (by linarith)
    have hqpos : 0 < y ^ 2 - w.im ^ 2 := by
      have hh := abs_lt.mp hw'
      nlinarith [mul_pos (sub_pos.mpr hh.2) (by linarith : 0 < y + w.im)]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hqpos (sq_pos_of_ne_zero ha))

/-- Principal inverse square root of the horizontal denominator. -/
def horizontalPoissonKernel (y : ℝ) (w c : ℂ) : ℂ :=
  horizontalPoissonDenom y w c ^ (-1 / 2 : ℂ)

/-- Complex derivative of the horizontal kernel on its holomorphic strip. -/
def horizontalPoissonDerivative (y : ℝ) (w c : ℂ) : ℂ :=
  (-1 / 2 : ℂ) * horizontalPoissonDenom y w c ^ ((-1 / 2 : ℂ) - 1) *
    (2 * (w * (c.im : ℂ) + (c.re : ℂ)) * (c.im : ℂ))

private lemma continuous_horizontalPoissonDenom (y : ℝ) :
    Continuous (fun p : ℂ × ℂ => horizontalPoissonDenom y p.1 p.2) := by
  unfold horizontalPoissonDenom
  fun_prop

private lemma continuousOn_horizontalPoissonKernel {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun p : ℂ × ℂ => horizontalPoissonKernel y p.1 p.2)
      (poissonHorizontalStrip y ×ˢ {c : ℂ | c ≠ 0}) :=
  (continuous_horizontalPoissonDenom y).continuousOn.cpow_const
    (fun _ hp => Or.inl (horizontalPoissonDenom_re_pos hy hp.1 hp.2))

private lemma continuousOn_horizontalPoissonDerivative {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun p : ℂ × ℂ => horizontalPoissonDerivative y p.1 p.2)
      (poissonHorizontalStrip y ×ˢ {c : ℂ | c ≠ 0}) := by
  have hp : ContinuousOn (fun p : ℂ × ℂ => horizontalPoissonDenom y p.1 p.2 ^ ((-1 / 2 : ℂ) - 1))
      (poissonHorizontalStrip y ×ˢ {c : ℂ | c ≠ 0}) :=
    (continuous_horizontalPoissonDenom y).continuousOn.cpow_const
      (fun _ hp => Or.inl (horizontalPoissonDenom_re_pos hy hp.1 hp.2))
  exact (continuousOn_const.mul hp).mul (by fun_prop)

/-- Exact complex derivative; compactness, rather than a new growth premise, bounds it. -/
theorem hasDerivAt_horizontalPoissonKernel {y : ℝ} (hy : 0 < y) {w c : ℂ}
    (hw : w ∈ poissonHorizontalStrip y) (hc : c ≠ 0) :
    HasDerivAt (fun v => horizontalPoissonKernel y v c) (horizontalPoissonDerivative y w c) w := by
  have hq : HasDerivAt (fun v => horizontalPoissonDenom y v c)
      (2 * (w * (c.im : ℂ) + (c.re : ℂ)) * (c.im : ℂ)) w := by
    simpa [horizontalPoissonDenom] using
      ((((hasDerivAt_id w).mul_const (c.im : ℂ)).add_const (c.re : ℂ)).pow 2).add_const
        (((y : ℂ) * (c.im : ℂ)) ^ 2)
  exact hq.cpow_const (Or.inl (horizontalPoissonDenom_re_pos hy hw hc))

/-- On real horizontal coordinates the holomorphic kernel is the actual real kernel. -/
theorem horizontalPoissonKernel_ofReal {y : ℝ} (hy : 0 < y) (x : ℝ) {c : ℂ} (hc : c ≠ 0) :
    horizontalPoissonKernel y (x : ℂ) c =
      (projectivePoissonKernel ((x : ℂ) + (y : ℂ) * I) c : ℂ) := by
  have hq : horizontalPoissonDenom y (x : ℂ) c =
      (projectivePoissonDenom ((x : ℂ) + (y : ℂ) * I) c : ℂ) := by
    simp [horizontalPoissonDenom, projectivePoissonDenom]
  have hp := projectivePoissonDenom_pos
    (z := (x : ℂ) + (y : ℂ) * I) (by simpa using hy) hc
  rw [horizontalPoissonKernel, hq, projectivePoissonKernel,
    Complex.ofReal_cpow hp.le]
  norm_num

private lemma circle_subset_punctured : sphere (0 : ℂ) 1 ⊆ {c : ℂ | c ≠ 0} := by
  intro c hc hz
  simp [hz] at hc

private lemma polarParameter_mem_circle (t : ℝ) : polarParameter t ∈ sphere (0 : ℂ) 1 := by
  simpa only [mem_sphere, dist_zero_right] using norm_polarParameter t

private lemma differentiableOn_weighted_horizontal {y : ℝ} (hy : 0 < y)
    {u : ℝ → ℝ} (hu : Integrable u) :
    DifferentiableOn ℂ (fun w => ∫ t : ℝ, u t • horizontalPoissonKernel y w (polarParameter t))
      (poissonHorizontalStrip y) := by
  intro w hw
  exact (hasDerivAt_weighted_compact_parameter (isOpen_poissonHorizontalStrip y) isOpen_ne
    (isCompact_sphere (0 : ℂ) 1) circle_subset_punctured continuous_polarParameter
    polarParameter_mem_circle hu (continuousOn_horizontalPoissonKernel hy)
    (continuousOn_horizontalPoissonDerivative hy)
    (fun _ hx _ hc => hasDerivAt_horizontalPoissonKernel hy hx hc) hw).differentiableAt.differentiableWithinAt

/-- Every actual polynomial mode is real analytic along every positive horizontal line. -/
theorem analyticOnNhd_polynomialPolarMode_line {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (P : ℂ[X]) {y : ℝ} (hy : 0 < y) :
    AnalyticOnNhd ℝ (fun x : ℝ => polynomialPolarMode ρ P ((x : ℂ) + (y : ℂ) * I)) univ := by
  let W : ℝ → ℂ := fun t => P.eval (Real.log |t| : ℂ) * polarKernel ρ I t
  have hW : Integrable W := integrable_polynomial_polarKernel hρ₀ hρ₁ (by simp) P
  let J : (ℝ → ℝ) → ℂ → ℂ :=
    fun u w => ∫ t : ℝ, u t • horizontalPoissonKernel y w (polarParameter t)
  let H : ℂ → ℂ := fun w => (Real.sqrt y : ℂ) *
    (J (fun t => (W t).re) w + I * J (fun t => (W t).im) w)
  have hJR : DifferentiableOn ℂ (J fun t => (W t).re) (poissonHorizontalStrip y) :=
    differentiableOn_weighted_horizontal hy hW.re
  have hJI : DifferentiableOn ℂ (J fun t => (W t).im) (poissonHorizontalStrip y) :=
    differentiableOn_weighted_horizontal hy hW.im
  have hH : DifferentiableOn ℂ H (poissonHorizontalStrip y) :=
    (differentiableOn_const _).mul (hJR.add ((differentiableOn_const _).mul hJI))
  have heq (x : ℝ) : H (x : ℂ) = polynomialPolarMode ρ P ((x : ℂ) + (y : ℂ) * I) := by
    have hx : (x : ℂ) ∈ poissonHorizontalStrip y := by simp [poissonHorizontalStrip]; positivity
    have hz : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy
    have hR : Integrable (fun t : ℝ => (W t).re • horizontalPoissonKernel y (x : ℂ) (polarParameter t)) :=
      weighted_parameter_integrable (isOpen_poissonHorizontalStrip y) isOpen_ne
        (isCompact_sphere (0 : ℂ) 1) circle_subset_punctured continuous_polarParameter
        polarParameter_mem_circle hW.re (continuousOn_horizontalPoissonKernel hy) hx
    have hI : Integrable (fun t : ℝ => I * ((W t).im • horizontalPoissonKernel y (x : ℂ) (polarParameter t))) :=
      (weighted_parameter_integrable (isOpen_poissonHorizontalStrip y) isOpen_ne
        (isCompact_sphere (0 : ℂ) 1) circle_subset_punctured continuous_polarParameter
        polarParameter_mem_circle hW.im (continuousOn_horizontalPoissonKernel hy) hx).const_mul I
    dsimp only [H, J, polynomialPolarMode]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero, zero_add]
    congr 1
    rw [← integral_const_mul, ← integral_add hR hI]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [horizontalPoissonKernel_ofReal hy x (circle_subset_punctured (polarParameter_mem_circle t)),
        polynomial_polarKernel_projective ρ _ P hz t]
      change (W t).re • _ + I * ((W t).im • _) = W t * _
      simp only [Complex.real_smul]
      calc
        _ = ((W t).re + (W t).im * I) *
            (projectivePoissonKernel ((x : ℂ) + (y : ℂ) * I) (polarParameter t) : ℂ) := by ring
        _ = _ := by rw [Complex.re_add_im]
  intro x _
  have hx : (x : ℂ) ∈ poissonHorizontalStrip y := by simp [poissonHorizontalStrip]; positivity
  have ha := MaassBesselSeries.analyticAt_ofReal_comp
    (hH.analyticAt ((isOpen_poissonHorizontalStrip y).mem_nhds hx))
  exact ha.congr (Eventually.of_forall heq)

end RHTower.WeilHigherDenominator
