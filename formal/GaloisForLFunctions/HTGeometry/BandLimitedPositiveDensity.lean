import Mathlib

/-!
# A positive band-limited density on the line

**Theorem** (`integral_cexp_mul_sincSq`). Put `g(y) = sinc(πy)²`. Then `0 ≤ g ≤ 1`, `g` is
continuous and integrable, and for every real `w`

`∫ e^{2πiyw} g(y) dy = max(0, 1 − |w|)`.

In particular `∫ g = 1` and `∫ e^{2πiyw} g(y) dy = 0` whenever `|w| ≥ 1`.

**Proof.** The indicator `χ` of `[−½, ½]` has Fourier transform `sinc(πy)`, and `χ ⋆ χ` is the
triangle `max(0, 1 − |x|)` (the length of `[−½, ½] ∩ [x − ½, x + ½]`). By the convolution theorem
the triangle has Fourier transform `g`. The triangle is continuous with compact support, and
`g(y) ≤ 2/(1 + π²y²)` is integrable, so Fourier inversion returns the triangle.
-/

open MeasureTheory Set Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity

/-- The indicator of `[−½, ½]`, real-valued. -/
def halfBoxReal : ℝ → ℝ := (Icc (-(1 / 2) : ℝ) (1 / 2)).indicator 1

/-- The indicator of `[−½, ½]`, complex-valued. -/
def halfBox (x : ℝ) : ℂ := (halfBoxReal x : ℂ)

/-- The triangle `max(0, 1 − |x|)`. -/
def triangle (x : ℝ) : ℝ := max 0 (1 - |x|)

/-- The band-limited density `sinc(πy)²`. -/
def sincSq (y : ℝ) : ℝ := Real.sinc (Real.pi * y) ^ 2

theorem sincSq_nonneg (y : ℝ) : 0 ≤ sincSq y := sq_nonneg _

theorem sincSq_le_one (y : ℝ) : sincSq y ≤ 1 := by
  have h := Real.abs_sinc_le_one (Real.pi * y)
  unfold sincSq
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) h

theorem continuous_sincSq : Continuous sincSq :=
  (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem continuous_triangle : Continuous triangle :=
  continuous_const.max (continuous_const.sub continuous_abs)

theorem triangle_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : triangle x = 0 :=
  max_eq_left (by linarith)

theorem triangle_zero : triangle 0 = 1 := by simp [triangle]

theorem hasCompactSupport_triangle : HasCompactSupport triangle := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => ?_
  refine triangle_eq_zero ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_halfBox : Integrable halfBox := by
  have h : Integrable halfBoxReal :=
    (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  exact h.ofReal

/-- `sinc(πy)² ≤ 2/(1 + π²y²)`. -/
theorem sincSq_le (y : ℝ) : sincSq y ≤ 2 * (1 + (Real.pi * y) ^ 2)⁻¹ := by
  set u := Real.pi * y
  have hpos : 0 < 1 + u ^ 2 := by positivity
  have h1 : sincSq y ≤ 1 := sincSq_le_one y
  by_cases hu : u = 0
  · rw [hu]; norm_num; linarith
  have hu2 : 0 < u ^ 2 := by positivity
  have h2 : sincSq y ≤ 1 / u ^ 2 := by
    unfold sincSq
    rw [Real.sinc_of_ne_zero hu, div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.sin_sq_le_one u]) hu2.le
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  by_cases hle : u ^ 2 ≤ 1
  · nlinarith [sincSq_nonneg y]
  · push Not at hle
    have : sincSq y * u ^ 2 ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h2 hu2.le
      rwa [one_div, inv_mul_cancel₀ hu2.ne'] at this
    nlinarith [sincSq_nonneg y]

theorem integrable_sincSq : Integrable sincSq := by
  have hI : Integrable (fun y : ℝ => 2 * (1 + (Real.pi * y) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' Real.pi_ne_zero).const_mul 2
  refine hI.mono' continuous_sincSq.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sincSq_nonneg y)]
  exact sincSq_le y

/-- **The Fourier transform of the half box.** `𝓕χ(y) = sinc(πy)`. -/
theorem fourier_halfBox (y : ℝ) : FourierTransform.fourier halfBox y = (Real.sinc (Real.pi * y) : ℂ) := by
  rw [Real.fourier_real_eq]
  have hfun : (fun v : ℝ => Real.fourierChar (-(v * y)) • halfBox v) =
      (Icc (-(1 / 2) : ℝ) (1 / 2)).indicator
        (fun v : ℝ => cexp ((-(2 * Real.pi * y) * I) * (v : ℂ))) := by
    funext v
    by_cases hv : v ∈ Icc (-(1 / 2) : ℝ) (1 / 2)
    · rw [indicator_of_mem hv]
      simp only [halfBox, halfBoxReal, indicator_of_mem hv, Pi.one_apply, Complex.ofReal_one,
        Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_one]
      congr 1; push_cast; ring
    · rw [indicator_of_notMem hv]
      simp only [halfBox, halfBoxReal]
      rw [indicator_of_notMem hv]
      simp
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  by_cases hy : y = 0
  · subst hy; norm_num
  have hc : (-(2 * Real.pi * y) * I : ℂ) ≠ 0 := by
    have : (2 * Real.pi * y : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 : ℝ) * Real.pi ≠ 0) |> fun h => mul_ne_zero h (by exact_mod_cast hy)
    simpa using this
  rw [integral_exp_mul_complex hc]
  have hpy : (Real.pi * y : ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hy
  rw [Real.sinc_of_ne_zero hpy]
  push_cast
  set z : ℂ := (Real.pi : ℂ) * y with hz
  have hz0 : z ≠ 0 := by rw [hz]; exact_mod_cast hpy
  have h1 : (-(2 * (Real.pi : ℂ) * y) * I) * (1 / 2) = -z * I := by rw [hz]; ring
  have h2 : (-(2 * (Real.pi : ℂ) * y) * I) * -(1 / 2) = z * I := by rw [hz]; ring
  rw [h1, h2]
  have hsin : Complex.sin z = (cexp (-z * I) - cexp (z * I)) * I / 2 := rfl
  rw [hsin]
  have hden : (-(2 * (Real.pi : ℂ) * y) * I) = -2 * z * I := by rw [hz]; ring
  rw [hden]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The half box convolved with itself is the triangle.** -/
theorem halfBox_convolution (x : ℝ) :
    convolution halfBox halfBox (ContinuousLinearMap.mul ℂ ℂ) volume x = (triangle x : ℂ) := by
  rw [convolution_def]
  have key : ∀ t, halfBoxReal (x - t) = (Icc (x - 1 / 2) (x + 1 / 2)).indicator 1 t := by
    intro t
    have hiff : x - t ∈ Icc (-(1 / 2) : ℝ) (1 / 2) ↔ t ∈ Icc (x - 1 / 2) (x + 1 / 2) := by
      simp only [mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases ht : t ∈ Icc (x - 1 / 2) (x + 1 / 2)
    · rw [halfBoxReal, indicator_of_mem (hiff.mpr ht), indicator_of_mem ht]; rfl
    · rw [halfBoxReal, indicator_of_notMem (fun h => ht (hiff.mp h)), indicator_of_notMem ht]
  have hfun : (fun t : ℝ => (ContinuousLinearMap.mul ℂ ℂ) (halfBox t) (halfBox (x - t))) =
      fun t => (((Icc (-(1 / 2) : ℝ) (1 / 2) ∩ Icc (x - 1 / 2) (x + 1 / 2)).indicator 1 t : ℝ) : ℂ) := by
    funext t
    simp only [ContinuousLinearMap.mul_apply', halfBox, key, inter_indicator_one, Pi.mul_apply]
    rw [halfBoxReal]
    push_cast
    ring
  rw [hfun, integral_complex_ofReal, integral_indicator_one (measurableSet_Icc.inter measurableSet_Icc),
    Icc_inter_Icc, Real.volume_real_Icc]
  congr 1
  unfold triangle
  rw [max_comm]
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right (by linarith), min_eq_left (by linarith)]; ring
  · rw [abs_of_nonpos hx, max_eq_left (by linarith), min_eq_right (by linarith)]; ring

/-- **The Fourier transform of the triangle is `sinc(πy)²`.** -/
theorem fourier_triangle (y : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (triangle x : ℂ)) y = (sincSq y : ℂ) := by
  have h : (fun x : ℝ => (triangle x : ℂ)) =
      convolution halfBox halfBox (ContinuousLinearMap.mul ℂ ℂ) volume :=
    funext fun x => (halfBox_convolution x).symm
  rw [h, Real.fourier_mul_convolution_eq integrable_halfBox integrable_halfBox, fourier_halfBox]
  simp [sincSq, sq]

/-- **Fourier inversion for the triangle.** `∫ e^{2πiyw} sinc(πy)² dy = max(0, 1 − |w|)`. -/
theorem integral_cexp_mul_sincSq (w : ℝ) :
    ∫ y : ℝ, cexp (((2 * Real.pi * y * w : ℝ) : ℂ) * I) * (sincSq y : ℂ) = (triangle w : ℂ) := by
  have hc : Continuous fun x : ℝ => (triangle x : ℂ) := continuous_ofReal.comp continuous_triangle
  have hi : Integrable fun x : ℝ => (triangle x : ℂ) :=
    (continuous_triangle.integrable_of_hasCompactSupport hasCompactSupport_triangle).ofReal
  have hF : FourierTransform.fourier (fun x : ℝ => (triangle x : ℂ)) = fun y => (sincSq y : ℂ) :=
    funext fourier_triangle
  have hFi : Integrable (FourierTransform.fourier fun x : ℝ => (triangle x : ℂ)) := by
    rw [hF]; exact integrable_sincSq.ofReal
  have hinv := hc.fourierInv_fourier_eq hi hFi
  have := congrFun hinv w
  rw [Real.fourierInv_eq', hF] at this
  rw [← this]
  congr 1
  funext y
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  ring_nf

theorem integral_cexp_mul_sincSq_eq_zero {w : ℝ} (hw : 1 ≤ |w|) :
    ∫ y : ℝ, cexp (((2 * Real.pi * y * w : ℝ) : ℂ) * I) * (sincSq y : ℂ) = 0 := by
  rw [integral_cexp_mul_sincSq, triangle_eq_zero hw, Complex.ofReal_zero]

theorem integral_sincSq : ∫ y : ℝ, sincSq y = 1 := by
  have h := integral_cexp_mul_sincSq 0
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, triangle_zero,
    Complex.ofReal_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

end GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity
