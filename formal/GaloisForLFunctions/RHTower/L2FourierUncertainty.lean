/-
BRIDGE (classical harmonic-analysis infrastructure).

Bounded-support Fourier uncertainty for `L²(ℝ)`, obtained by combining the unconditional
classical `L¹` uncertainty theorem with the checked comparison between mathlib's unitary `L²`
Fourier transform and the classical Fourier integral on integrable representatives.
-/
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

noncomputable section

open MeasureTheory
open FourierTransform
open Set
open scoped ENNReal

namespace RHTower

/-- An `L²(ℝ)` function and its unitary `L²` Fourier transform cannot both have bounded
essential support unless the `L²` function is zero. -/
theorem l2_fourier_uncertainty
    (f : Lp ℂ 2 (volume : Measure ℝ)) {a b : ℝ}
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → (f : ℝ → ℂ) x = 0)
    (hF : ∀ᵐ w ∂volume, w ∉ Icc (-b) b →
      (((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w = 0)) :
    f = 0 := by
  have hfOn : IntegrableOn (f : ℝ → ℂ) (Icc (-a) a) volume :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc
  have hf : Integrable (f : ℝ → ℂ) :=
    hfOn.integrable_of_ae_notMem_eq_zero hs
  let f₁ : Lp ℂ 1 (volume : Measure ℝ) :=
    (memLp_one_iff_integrable.mpr hf).toLp f
  have hcoe : (f₁ : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)
  have hclassical : ∀ w : ℝ,
      (Real.Lp.fourierTransform f₁ : ℝ → ℂ) w =
        FourierTransform.fourier (f : ℝ → ℂ) w := by
    intro w
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hcoe w
  have hFourierAe :
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        FourierTransform.fourier (f : ℝ → ℂ) :=
    (l2_fourier_coeFn_eq_l1_fourier_of_integrable f hf).trans
      (Filter.Eventually.of_forall hclassical)
  have hClassicalSupport : ∀ᵐ w ∂volume,
      w ∉ Icc (-b) b → FourierTransform.fourier (f : ℝ → ℂ) w = 0 := by
    filter_upwards [hF, hFourierAe] with w hw hEq hOutside
    rw [← hEq]
    exact hw hOutside
  have hzero : (f : ℝ → ℂ) =ᵐ[volume] 0 :=
    integrable_fourier_uncertainty hf hs hClassicalSupport
  apply Lp.ext
  filter_upwards [hzero] with x hx
  simpa using hx

/-- A bounded-support `L²(ℝ)` function whose unitary Fourier transform vanishes almost
everywhere on one nonempty open interval is zero.  Unlike `l2_fourier_uncertainty`, no bounded
support assumption is made on the Fourier transform away from that interval. -/
theorem l2_eq_zero_of_bounded_support_fourier_vanishes_on_Ioo
    (f : Lp ℂ 2 (volume : Measure ℝ)) {a c d : ℝ}
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (-a) a → (f : ℝ → ℂ) x = 0)
    (hcd : c < d)
    (hF : ∀ᵐ w ∂volume, w ∈ Ioo c d →
      (((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w = 0)) :
    f = 0 := by
  have hfOn : IntegrableOn (f : ℝ → ℂ) (Icc (-a) a) volume :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc
  have hf : Integrable (f : ℝ → ℂ) :=
    hfOn.integrable_of_ae_notMem_eq_zero hs
  let f₁ : Lp ℂ 1 (volume : Measure ℝ) :=
    (memLp_one_iff_integrable.mpr hf).toLp f
  have hcoe : (f₁ : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)
  have hclassical : ∀ w : ℝ,
      (Real.Lp.fourierTransform f₁ : ℝ → ℂ) w =
        FourierTransform.fourier (f : ℝ → ℂ) w := by
    intro w
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hcoe w
  have hFourierAe :
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        FourierTransform.fourier (f : ℝ → ℂ) :=
    (l2_fourier_coeFn_eq_l1_fourier_of_integrable f hf).trans
      (Filter.Eventually.of_forall hclassical)
  have hClassicalOpen : ∀ᵐ w ∂volume,
      w ∈ Ioo c d → FourierTransform.fourier (f : ℝ → ℂ) w = 0 := by
    filter_upwards [hF, hFourierAe] with w hw hEq hInside
    rw [← hEq]
    exact hw hInside
  have hFourierZero : ∀ w : ℝ,
      FourierTransform.fourier (f : ℝ → ℂ) w = 0 :=
    fourier_eq_zero_of_ae_zero_on_Ioo hf hs hcd hClassicalOpen
  have hzero : (f : ℝ → ℂ) =ᵐ[volume] 0 :=
    integrable_ae_eq_zero_of_fourier_eq_zero hf hFourierZero
  apply Lp.ext
  filter_upwards [hzero] with x hx
  simpa using hx

end RHTower
