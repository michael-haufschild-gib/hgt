import GaloisForLFunctions.RHTower.Suzuki.SuzukiClarkMeasure
import GaloisForLFunctions.HTGeometry.L2FourierIntegralBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

/-!
# The Cauchy kernel as a Fourier transform

For a point `w` strictly below the real axis, the kernel `ξ ↦ 1/(ξ - w)` is the Fourier transform
of the one-sided exponential

```text
t ↦ 1_{(-∞,0)}(t) · (-2πi) · exp (2πi w t),
```

which is integrable and square-integrable exactly because `Im w < 0` makes the exponent decay as
`t → -∞`.  Since the datum is supported on the negative ray, the kernel lies in the Hardy space of
the upper half-plane in the boundary realization used here.

This is the entry point for the reproducing property of the model space: pairing an element of
`K(Θ)` against `1/(· - w̄)` computes its value at `w`.
-/

open MeasureTheory Set Complex Filter Topology FourierTransform

namespace RHTower

/-- The one-sided exponential whose Fourier transform is the Cauchy kernel at `w`. -/
def cauchyDatum (w : ℂ) : ℝ → ℂ :=
  Set.indicator (Set.Iio (0 : ℝ))
    (fun t : ℝ => (-(2 * (Real.pi : ℂ) * I)) *
      Complex.exp (2 * (Real.pi : ℂ) * I * w * (t : ℂ)))

/-- The decay rate of the datum. -/
def cauchyRate (w : ℂ) : ℝ := -(2 * Real.pi * w.im)

theorem cauchyRate_pos {w : ℂ} (hw : w.im < 0) : 0 < cauchyRate w := by
  have := Real.pi_pos
  simp only [cauchyRate]
  nlinarith

theorem re_cauchyExponent (w : ℂ) (t : ℝ) :
    (2 * (Real.pi : ℂ) * I * w * (t : ℂ)).re = cauchyRate w * t := by
  simp only [cauchyRate]
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_cauchyDatum (w : ℂ) (t : ℝ) :
    ‖cauchyDatum w t‖
      = Set.indicator (Set.Iio (0 : ℝ))
        (fun t : ℝ => 2 * Real.pi * Real.exp (cauchyRate w * t)) t := by
  rcases lt_or_ge t 0 with h | h
  · have hmem : t ∈ Set.Iio (0 : ℝ) := Set.mem_Iio.mpr h
    rw [cauchyDatum, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, norm_mul,
      Complex.norm_exp, re_cauchyExponent]
    congr 1
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  · have hnot : t ∉ Set.Iio (0 : ℝ) := by simpa using h
    rw [cauchyDatum, Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot, norm_zero]

theorem integrable_cauchyDatum {w : ℂ} (hw : w.im < 0) : Integrable (cauchyDatum w) volume := by
  have hb := cauchyRate_pos hw
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (cauchyRate w * t)) (Set.Iic (0 : ℝ)) :=
    integrableOn_exp_mul_Iic hb 0
  have h1 : IntegrableOn (fun t : ℝ => 2 * Real.pi * Real.exp (cauchyRate w * t))
      (Set.Iic (0 : ℝ)) := Integrable.const_mul h0 (2 * Real.pi)
  have hmaj : IntegrableOn (fun t : ℝ => 2 * Real.pi * Real.exp (cauchyRate w * t))
      (Set.Iio (0 : ℝ)) := h1.mono_set Set.Iio_subset_Iic_self
  have hmajall : Integrable (Set.indicator (Set.Iio (0 : ℝ))
      (fun t : ℝ => 2 * Real.pi * Real.exp (cauchyRate w * t))) volume :=
    (integrable_indicator_iff measurableSet_Iio).mpr hmaj
  refine Integrable.mono' hmajall ?_ ?_
  · refine AEStronglyMeasurable.indicator ?_ measurableSet_Iio
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  · filter_upwards with t
    rw [norm_cauchyDatum]

theorem re_cauchyShiftExponent (w : ℂ) (ξ : ℝ) :
    (2 * (Real.pi : ℂ) * I * (w - (ξ : ℂ))).re = cauchyRate w := by
  simp only [cauchyRate]
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]

/-- **The Cauchy kernel is the Fourier transform of a one-sided exponential.** -/
theorem fourierIntegral_cauchyDatum {w : ℂ} (hw : w.im < 0) (ξ : ℝ) :
    𝓕 (cauchyDatum w) ξ = (((ξ : ℝ) : ℂ) - w)⁻¹ := by
  have hb := cauchyRate_pos hw
  have ha : (0 : ℝ) < (2 * (Real.pi : ℂ) * I * (w - (ξ : ℂ))).re := by
    rw [re_cauchyShiftExponent]
    exact hb
  have hane : (2 * (Real.pi : ℂ) * I * (w - (ξ : ℂ))) ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hpt : ∀ t : ℝ,
      (Real.fourierChar (-(inner ℝ t ξ)) : ℂ) * cauchyDatum w t
        = Set.indicator (Set.Iio (0 : ℝ))
          (fun t : ℝ => (-(2 * (Real.pi : ℂ) * I)) *
            Complex.exp (2 * (Real.pi : ℂ) * I * (w - (ξ : ℂ)) * (t : ℂ))) t := by
    intro t
    rcases lt_or_ge t 0 with h | h
    · have hmem : t ∈ Set.Iio (0 : ℝ) := Set.mem_Iio.mpr h
      rw [cauchyDatum, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        Real.fourierChar_apply]
      rw [show (-(inner ℝ t ξ) : ℝ) = -(t * ξ) by simp [mul_comm]]
      rw [show Complex.exp (((2 * Real.pi * -(t * ξ) : ℝ) : ℂ) * I)
            * (-(2 * (Real.pi : ℂ) * I) * Complex.exp (2 * (Real.pi : ℂ) * I * w * (t : ℂ)))
          = (-(2 * (Real.pi : ℂ) * I))
            * (Complex.exp (((2 * Real.pi * -(t * ξ) : ℝ) : ℂ) * I)
              * Complex.exp (2 * (Real.pi : ℂ) * I * w * (t : ℂ))) by ring]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hnot : t ∉ Set.Iio (0 : ℝ) := by simpa using h
      rw [cauchyDatum, Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot, mul_zero]
  rw [Real.fourier_eq]
  have hsmul : ∀ t : ℝ, (Real.fourierChar (-(inner ℝ t ξ))) • cauchyDatum w t
      = (Real.fourierChar (-(inner ℝ t ξ)) : ℂ) * cauchyDatum w t := fun t => rfl
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun t => (hsmul t).trans (hpt t)))]
  rw [MeasureTheory.integral_indicator measurableSet_Iio]
  rw [MeasureTheory.setIntegral_congr_set Iio_ae_eq_Iic]
  rw [MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Iic ha 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  rw [show ((ξ : ℂ) - w) = -(w - (ξ : ℂ)) by ring, one_div, one_div, inv_neg]


theorem norm_cauchyDatum_le {w : ℂ} (hw : w.im < 0) (t : ℝ) :
    ‖cauchyDatum w t‖ ≤ 2 * Real.pi := by
  have hb := cauchyRate_pos hw
  rcases lt_or_ge t 0 with h | h
  · have hmem : t ∈ Set.Iio (0 : ℝ) := Set.mem_Iio.mpr h
    rw [norm_cauchyDatum, Set.indicator_of_mem hmem]
    have hexp : Real.exp (cauchyRate w * t) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      nlinarith
    nlinarith [Real.pi_pos, Real.exp_pos (cauchyRate w * t)]
  · have hnot : t ∉ Set.Iio (0 : ℝ) := by simpa using h
    rw [norm_cauchyDatum, Set.indicator_of_notMem hnot]
    positivity

theorem memLp_cauchyDatum {w : ℂ} (hw : w.im < 0) :
    MemLp (cauchyDatum w) 2 (volume : Measure ℝ) := by
  have hint := integrable_cauchyDatum hw
  refine (memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' (hint.norm.const_mul (2 * Real.pi)) ?_ ?_
  · exact (hint.aestronglyMeasurable.norm.pow 2)
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right (norm_cauchyDatum_le hw t) (norm_nonneg _)

theorem cauchyDatum_mem_lowerHalfLineL2 {w : ℂ} (hw : w.im < 0) :
    (memLp_cauchyDatum hw).toLp _ ∈ lowerHalfLineL2 := by
  rw [mem_lowerHalfLineL2_iff]
  filter_upwards [(memLp_cauchyDatum hw).coeFn_toLp] with x h1 hx
  rw [h1, cauchyDatum, Set.indicator_of_notMem (by simpa using hx.le)]


/-! ## The kernel itself -/

theorem norm_sq_cauchyKernel (w : ℂ) (ξ : ℝ) :
    ‖(((ξ : ℝ) : ℂ) - w)⁻¹‖ ^ (2 : ℕ) = ((ξ - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ))⁻¹ := by
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp [Complex.sub_re, Complex.sub_im]
  ring

theorem integrable_cauchyKernelSq {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun ξ : ℝ => ((ξ - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ))⁻¹) volume := by
  have hb : (w.im)⁻¹ ≠ 0 := inv_ne_zero hw
  have h1 : Integrable (fun u : ℝ => (1 + ((w.im)⁻¹ * u) ^ (2 : ℕ))⁻¹) volume :=
    integrable_inv_one_add_sq.comp_mul_left' hb
  have h2 : Integrable (fun ξ : ℝ => (1 + ((w.im)⁻¹ * (ξ - w.re)) ^ (2 : ℕ))⁻¹) volume :=
    h1.comp_sub_right w.re
  refine (h2.const_mul ((w.im ^ (2 : ℕ))⁻¹)).congr ?_
  filter_upwards with ξ
  have hi2 : (w.im) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hw
  field_simp
  ring

theorem memLp_cauchyKernel {w : ℂ} (hw : w.im ≠ 0) :
    MemLp (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - w)⁻¹) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - w)⁻¹) volume := by
    refine Measurable.aestronglyMeasurable ?_
    exact (Complex.measurable_ofReal.sub measurable_const).inv
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  refine (integrable_cauchyKernelSq hw).congr ?_
  filter_upwards with ξ
  exact (norm_sq_cauchyKernel w ξ).symm

/-- The Cauchy kernel below the axis is the `L²` Fourier transform of the one-sided exponential
`cauchyDatum`. -/
theorem fourierTransform_cauchyDatum {w : ℂ} (hw : w.im < 0) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap
        ((memLp_cauchyDatum hw).toLp (cauchyDatum w)) : Lp ℂ 2 (volume : Measure ℝ))
      = (memLp_cauchyKernel (ne_of_lt hw)).toLp
          (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - w)⁻¹) := by
  have hint : Integrable (((memLp_cauchyDatum hw).toLp (cauchyDatum w)) : ℝ → ℂ) :=
    (integrable_cauchyDatum hw).congr (memLp_cauchyDatum hw).coeFn_toLp.symm
  refine MeasureTheory.Lp.ext ?_
  have hbridge := GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_ae_eq_fourierIntegral
    ((memLp_cauchyDatum hw).toLp (cauchyDatum w)) hint
  have hclass : ∀ ξ : ℝ,
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp
        (((memLp_cauchyDatum hw).toLp (cauchyDatum w)) : ℝ → ℂ)) : ℝ → ℂ) ξ
        = (((ξ : ℝ) : ℂ) - w)⁻¹ := by
    intro ξ
    rw [Real.Lp.fourierTransform_apply, ← fourierIntegral_cauchyDatum hw ξ]
    have hae : (((memLp_one_iff_integrable.mpr hint).toLp
        (((memLp_cauchyDatum hw).toLp (cauchyDatum w)) : ℝ → ℂ)) : ℝ → ℂ)
        =ᵐ[volume] cauchyDatum w :=
      ((memLp_one_iff_integrable.mpr hint).coeFn_toLp).trans
        (memLp_cauchyDatum hw).coeFn_toLp
    rw [Real.fourier_eq, Real.fourier_eq]
    exact MeasureTheory.integral_congr_ae (hae.mono fun t ht => by simp only [ht])
  have hbridge' : (((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap
      ((memLp_cauchyDatum hw).toLp (cauchyDatum w)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ =>
        (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp
          (((memLp_cauchyDatum hw).toLp (cauchyDatum w)) : ℝ → ℂ))) ξ := hbridge
  filter_upwards [hbridge', (memLp_cauchyKernel (ne_of_lt hw)).coeFn_toLp] with ξ h1 h2
  rw [h1, hclass ξ, h2]

/-- **The Cauchy kernel below the axis lies in the Hardy space.** -/
theorem cauchyKernel_mem_hardyL2 {w : ℂ} (hw : w.im < 0) :
    (memLp_cauchyKernel (ne_of_lt hw)).toLp _ ∈ hardyL2 := by
  exact ⟨(memLp_cauchyDatum hw).toLp _, cauchyDatum_mem_lowerHalfLineL2 hw,
    fourierTransform_cauchyDatum hw⟩


end RHTower
