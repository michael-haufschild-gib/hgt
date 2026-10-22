import GaloisForLFunctions.HTGeometry.L2NegativeHalfLineExtension
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceVectorLaplace

/-! The three actual causal principal forcings, preserving the original radial source. -/
open MeasureTheory Set Filter GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore
noncomputable section

theorem timeRadialSourceVector_zero_of_nonpos (s a : ℂ) (τ : ℝ) (hτ : τ ≤ 0) :
    timeRadialSourceVector s a τ = 0 := by
  apply Lp.ext
  filter_upwards [timeRadialSourceVector_ae s a τ,ae_restrict_mem measurableSet_Iio,
    Lp.coeFn_zero ℂ 2 radialMeasure] with t ht ht₀ hz
  rw [ht,hz]
  exact timeReducedCoefficient_zero_before_onset s a τ t (by change t < 0 at ht₀; linarith)

/-- Each forcing is the literal principal amplitude times the odd extension of the native source. -/
def principalTimeForcing (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    FourierRealL2 :=
  principalAmplitude q i • negativeOddExtension (timeRadialSourceVector (physicalRate q branch) a τ)

theorem principalTimeForcing_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (principalTimeForcing q branch a i) := by
  change Continuous (fun τ => principalAmplitude q i •
    negativeOddExtension (timeRadialSourceVector (physicalRate q branch) a τ))
  exact (continuous_const : Continuous (fun _ : ℝ => principalAmplitude q i)).smul
    (negativeOddExtension.continuous.comp (timeRadialSourceVector_continuous q branch a))

theorem principalTimeForcing_zero_of_nonpos (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (τ : ℝ) (hτ : τ ≤ 0) : principalTimeForcing q branch a i τ = 0 := by
  simp only [principalTimeForcing,timeRadialSourceVector_zero_of_nonpos _ _ τ hτ,map_zero,smul_zero]

theorem principalTimeForcing_reflection (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    l2Reflection (principalTimeForcing q branch a i τ) = -principalTimeForcing q branch a i τ := by
  simp only [principalTimeForcing,map_smul,negativeOddExtension_reflection,smul_neg]

/-- The whole-line construction retains the exact original forcing on the physical negative ray. -/
theorem principalTimeForcing_ae_negative (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    principalTimeForcing q branch a i τ =ᵐ[radialMeasure]
      (fun t => principalAmplitude q i*timeReducedCoefficient (physicalRate q branch) a τ t) := by
  have hs := (Lp.coeFn_smul (principalAmplitude q i)
    (negativeOddExtension (timeRadialSourceVector (physicalRate q branch) a τ))).filter_mono
      (ae_mono (show radialMeasure ≤ volume from Measure.restrict_le_self))
  filter_upwards [hs,negativeOddExtension_ae_negative
    (timeRadialSourceVector (physicalRate q branch) a τ),
    timeRadialSourceVector_ae (physicalRate q branch) a τ] with t hs he ht
  change (principalAmplitude q i • negativeOddExtension
    (timeRadialSourceVector (physicalRate q branch) a τ)) t = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,he,ht]

theorem principalTimeForcing_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : -2 < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • principalTimeForcing q branch a i τ) (Ioi 0) := by
  let L : NegativeLineL2 →L[ℂ] FourierRealL2 := principalAmplitude q i • negativeOddExtension
  apply (L.integrable_comp (timeRadialSourceVector_laplace_integrable q branch a w hw)).congr
  filter_upwards [] with τ
  rw [map_smul]
  rfl

theorem principalTimeForcing_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    IntegrableOn (principalTimeForcing q branch a i) (Ioi 0) := by
  simpa using principalTimeForcing_laplace_integrable q branch a i 0 (by norm_num)

/-- Actual forcing transforms, with the original onset factor retained and no frequency-dependent time family. -/
theorem principalTimeForcing_laplace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : -2 < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • principalTimeForcing q branch a i τ) =
      principalAmplitude q i • negativeOddExtension (radialSourceLaplaceVector q branch a w hw) := by
  let L : NegativeLineL2 →L[ℂ] FourierRealL2 := principalAmplitude q i • negativeOddExtension
  have he (τ : ℝ) : Complex.exp (-w*(τ:ℂ)) • principalTimeForcing q branch a i τ =
      L (Complex.exp (-w*(τ:ℂ)) • timeRadialSourceVector (physicalRate q branch) a τ) := by
    rw [map_smul]
    rfl
  simp only [he]
  rw [L.integral_comp_comm (timeRadialSourceVector_laplace_integrable q branch a w hw),
    timeRadialSourceVector_laplace]
  rfl

end
end RHTower.D4BMJointSource
