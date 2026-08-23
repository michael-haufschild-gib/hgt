import GaloisForLFunctions.RHTower.SoninBandCodimensionTwo
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.RHTower.SoninProjectionCalkin

/-!
# The Fourier partner of the band indicator is the sinc kernel

`fourierBandIndicator a = 𝓕⁻¹(1_{[-a,a]})` is the unique vector whose Fourier transform is the
band indicator, so it is the correction that turns a vector of the extended Sonine space `L_a` into
one whose Fourier transform vanishes on the band.  Everything downstream needs its pointwise shape

`fourierBandIndicator a (t) = sin(2πat)/(πt)`,

whose `1/|t|` decay is what makes its Mellin tail converge on the whole half-plane `Re s > 0`.

## Main results

* `fourierIntegral_centralIndicator` — the explicit Fourier integral of `1_{[-a,a]}`
* `coeFn_fourierBandIndicator_ae` — the sinc formula
* `norm_coeFn_fourierBandIndicator_le` — the `1/(π|t|)` bound
-/

noncomputable section

open MeasureTheory Set Filter Topology FourierTransform

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem integrable_centralIndicator (a : ℝ) :
    Integrable ((centralInterval a).indicator fun _ => (1 : ℂ)) volume := by
  rw [integrable_indicator_iff (measurableSet_centralInterval a), centralInterval]
  exact integrableOn_const measure_Icc_lt_top.ne

theorem integrable_bandIndicator (a : ℝ) :
    Integrable ((bandIndicator a : SoninL2) : ℝ → ℂ) volume :=
  (integrable_centralIndicator a).congr (bandIndicator_coeFn a).symm

/-- **The Fourier integral of the symmetric band indicator.** -/
theorem fourierIntegral_centralIndicator {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : u ≠ 0) :
    𝓕 ((centralInterval a).indicator fun _ => (1 : ℂ)) u
      = ((Real.sin (2 * Real.pi * a * u) / (Real.pi * u) : ℝ) : ℂ) := by
  have hstep : 𝓕 ((centralInterval a).indicator fun _ => (1 : ℂ)) u
      = ∫ v in Set.Icc (-a) a, Complex.exp ((((-2 * Real.pi * u : ℝ)) : ℂ) * Complex.I * (v : ℂ)) := by
    have hpt : ∀ v : ℝ,
        Complex.exp ((((-2 * Real.pi * v * u : ℝ)) : ℂ) * Complex.I)
            • (centralInterval a).indicator (fun _ => (1 : ℂ)) v
          = (Set.Icc (-a) a).indicator
              (fun v : ℝ => Complex.exp ((((-2 * Real.pi * u : ℝ)) : ℂ) * Complex.I * (v : ℂ))) v := by
      intro v
      by_cases hv : v ∈ Set.Icc (-a) a
      · have hv' : v ∈ centralInterval a := by rwa [centralInterval]
        rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv', smul_eq_mul, mul_one]
        congr 1
        push_cast
        ring
      · have hv' : v ∉ centralInterval a := by rwa [centralInterval]
        rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv', smul_zero]
    rw [Real.fourier_real_eq_integral_exp_smul,
      integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_indicator measurableSet_Icc]
  set c : ℂ := (((-2 * Real.pi * u : ℝ)) : ℂ) * Complex.I with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    rcases mul_eq_zero.1 h with h1 | h2
    · rcases mul_eq_zero.1 h1 with h3 | h4
      · norm_num at h3
      · exact this h4
    · exact hu h2
  have hicc : (∫ v in Set.Icc (-a) a, Complex.exp (c * (v : ℂ)))
      = (Complex.exp (c * (a : ℂ)) - Complex.exp (c * ((-a : ℝ) : ℂ))) / c := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-a : ℝ) ≤ a)]
    exact integral_exp_mul_complex hcne
  rw [hstep, hicc]
  set z : ℂ := ((2 * Real.pi * u * a : ℝ) : ℂ) with hz
  have hca : c * (a : ℂ) = -z * Complex.I := by
    rw [hc, hz]; push_cast; ring
  have hcna : c * ((-a : ℝ) : ℂ) = z * Complex.I := by
    rw [hc, hz]; push_cast; ring
  rw [hca, hcna]
  have hsindef : Complex.sin z
      = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 := rfl
  have hnum : Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)
      = -(2 * Complex.I) * Complex.sin z := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [hsindef]
    linear_combination (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * hI
  rw [hnum, hc]
  have hpne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu
  have hzval : Complex.sin z = ((Real.sin (2 * Real.pi * a * u) : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sin]
    congr 2
    ring
  rw [hzval, Complex.ofReal_div, Complex.ofReal_mul]
  push_cast
  field_simp

theorem ae_ne_zero : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ 0 := by
  have hset : {t : ℝ | ¬ (t ≠ 0)} = {(0 : ℝ)} := by
    ext t
    simp
  rw [MeasureTheory.ae_iff, hset]
  simp

theorem coeFn_fourierUnitary_bandIndicator (a : ℝ) :
    ((fourierUnitary (bandIndicator a) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] 𝓕 ((centralInterval a).indicator fun _ => (1 : ℂ)) := by
  have hint : Integrable ((bandIndicator a : SoninL2) : ℝ → ℂ) := integrable_bandIndicator a
  have hbridge := l2_fourier_coeFn_eq_l1_fourier_of_integrable (bandIndicator a) hint
  refine hbridge.trans ?_
  have h1 : (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp
        ((bandIndicator a : SoninL2) : ℝ → ℂ)) : ℝ → ℂ)
      = 𝓕 ((bandIndicator a : SoninL2) : ℝ → ℂ) := Real.fourierTransform_toLp _
  rw [h1]
  exact Filter.Eventually.of_forall (Real.fourier_congr_ae (bandIndicator_coeFn a))

/-- **The Fourier partner of the band indicator is the sinc kernel.** -/
theorem coeFn_fourierBandIndicator_ae {a : ℝ} (ha : 0 < a) :
    ((fourierBandIndicator a : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => ((Real.sin (2 * Real.pi * a * t) / (Real.pi * t) : ℝ) : ℂ) := by
  have hsymm : fourierBandIndicator a = l2Reflection (fourierUnitary (bandIndicator a)) := by
    rw [fourierBandIndicator, fourierUnitary_symm_eq_reflection_fourier]
  have hrefl : ((fourierBandIndicator a : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => ((fourierUnitary (bandIndicator a) : SoninL2) : ℝ → ℂ) (-t) := by
    rw [hsymm]
    exact l2Reflection_ae _
  have hpull := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (coeFn_fourierUnitary_bandIndicator a)
  filter_upwards [hrefl, hpull, ae_ne_zero] with t h1 h2 h3
  rw [h1, h2, fourierIntegral_centralIndicator ha (neg_ne_zero.2 h3)]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  congr 1
  rw [show 2 * Real.pi * a * -t = -(2 * Real.pi * a * t) from by ring, Real.sin_neg]
  field_simp

/-- **The sinc decay.** -/
theorem norm_coeFn_fourierBandIndicator_le {a : ℝ} (ha : 0 < a) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      ‖((fourierBandIndicator a : SoninL2) : ℝ → ℂ) t‖ ≤ 1 / (Real.pi * |t|) := by
  filter_upwards [coeFn_fourierBandIndicator_ae ha, ae_ne_zero] with t h1 h2
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos Real.pi_pos]
  have habs : (0 : ℝ) < Real.pi * |t| := by
    refine mul_pos Real.pi_pos ?_
    exact abs_pos.2 h2
  have hsin : |Real.sin (2 * Real.pi * a * t)| ≤ 1 := Real.abs_sin_le_one _
  gcongr

end RHTower

end
