import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2MixedSourceLimit
import GaloisForLFunctions.RHTower.CCM.CCMSuzukiV2ProjectiveRawCarrier

open Complex MeasureTheory Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower
attribute [local instance] Measure.Subtype.measureSpace

/-- Actual interval spectral evaluation at a general imaginary point is the
literal real exponential source. -/
theorem suzukiTaSpectralExponentialL2_imaginary
    (a : SuzukiPositiveAperture) (s : ℝ) :
    suzukiTaSpectralExponentialL2 a (I * (s : ℂ)) = suzukiTaExponentialL2 a s := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaSpectralExponentialContinuous a (I * (s : ℂ))),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaExponentialContinuous a s)] with x hx hy
  change (((ContinuousMap.toLp 2 volume ℂ)
      (suzukiTaSpectralExponentialContinuous a (I * (s : ℂ))) :
        SuzukiApertureInterval a.1 → ℂ) x) =
    (((ContinuousMap.toLp 2 volume ℂ) (suzukiTaExponentialContinuous a s) :
      SuzukiApertureInterval a.1 → ℂ) x)
  rw [hx, hy]
  change Complex.exp (-I * (I * (s : ℂ)) * ((x : ℝ) : ℂ)) =
    (Real.exp (s * (x : ℝ)) : ℂ)
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  have hI : (-I : ℂ) * I = 1 := by rw [neg_mul, I_mul_I]; norm_num
  calc
    _ = ((-I : ℂ) * I) * ((s : ℂ) * ((x : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hI, one_mul]

/-- Imaginary spectral evaluation keeps the exact actual interval/aperture
unitary and Fourier sign convention. -/
theorem suzukiTaPhysicalFourier_imaginary_eq_polar_pairing
    (a : SuzukiPositiveAperture) (w : SuzukiTaHilbert a) (s : ℝ) :
    suzukiTaPhysicalFourier a w (I * (s : ℂ)) =
      inner ℂ (ccmPolarApertureVector a (-s))
        (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a w)) := by
  rw [← suzukiTaSpectralMoment_star_eq_physicalFourier]
  have hstar : star (I * (s : ℂ)) = I * ((-s : ℝ) : ℂ) := by simp
  rw [hstar, suzukiTaSpectralMoment, ContinuousLinearMap.comp_apply,
    suzukiTaSpectralExponentialL2_imaginary]
  let e := suzukiApertureL2Equiv a
  have hp : e (suzukiTaExponentialL2 a (-s)) = ccmPolarApertureVector a (-s) := by
    apply Subtype.ext
    exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a (-s)
  have hf : ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a w) =
      e (suzukiTaPhysicalEmbedding a w) := by
    change _ = e (e.symm _)
    rw [e.apply_symm_apply]
    rfl
  rw [← hp, hf, e.inner_map_map]
  rfl

/-- Exact actual carrier ratio on the imaginary axis. -/
theorem suzukiTaV2Livsic_imaginary_eq_mixed_pairing
    (a : SuzukiPositiveAperture) (s : ℝ) :
    suzukiTaV2Livsic a (I * (s : ℂ)) =
      ((I * (s : ℂ) - I) / (I * (s : ℂ) + I)) *
        (suzukiTaV2MixedSourcePairing a (-s) / suzukiTaV2MixedSourcePairing a s) := by
  rw [suzukiTaV2Livsic_eq_rawDeficiency]
  unfold suzukiLivsicQuotient suzukiTaV2RawCharacteristicA suzukiTaV2RawCharacteristicE
  rw [suzukiTaPhysicalFourier_rawDeficiency_reflection]
  rw [show -(I * (s : ℂ)) = I * ((-s : ℝ) : ℂ) by push_cast; ring]
  rw [suzukiTaPhysicalFourier_imaginary_eq_polar_pairing,
    suzukiTaPhysicalFourier_imaginary_eq_polar_pairing, neg_neg]
  exact mul_div_mul_comm _ _ _ _

/-- Actual prescribed-shift Livsic collapse on an interior imaginary segment.
No source, normalization or convergence premise is assumed. -/
theorem tendsto_suzukiTaV2Livsic_imaginary_zero
    (s : Set.Ioo (1 / 2 : ℝ) 1) :
    Tendsto (fun a : SuzukiPositiveAperture => suzukiTaV2Livsic a (I * (s.1 : ℂ)))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  obtain ⟨hp, hm⟩ := tendsto_suzukiTaV2_scaled_mixed_source_pairings s
  have hlim : ((1 / (1 + s.1) : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply div_ne_zero one_ne_zero
    linarith [s.2.1]
  have hscaled := hm.div hp hlim
  have hscale (a : SuzukiPositiveAperture) : (suzukiTaV2MixedSourceScale a s.1 : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (mul_pos (boundedPerturbedFormShift_pos _) (Real.exp_pos _)).ne'
  have hratio := hscaled.congr' (Eventually.of_forall fun a =>
    mul_div_mul_left (suzukiTaV2MixedSourcePairing a (-s.1))
      (suzukiTaV2MixedSourcePairing a s.1) (hscale a))
  have h := hratio.const_mul ((I * (s.1 : ℂ) - I) / (I * (s.1 : ℂ) + I))
  simpa only [suzukiTaV2Livsic_imaginary_eq_mixed_pairing, zero_div, mul_zero] using h

end RHTower
end
