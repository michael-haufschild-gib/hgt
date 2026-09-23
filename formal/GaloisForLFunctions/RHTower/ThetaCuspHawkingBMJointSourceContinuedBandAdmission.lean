import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedRadialAdmission
import GaloisForLFunctions.HTGeometry.L2FamilyCongruence

/-! Admission of the same original continued cutoff throughout a band crossing the source chamber. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The physical onset pole lies strictly to the left of the entire continuation band. -/
theorem physicalSourceDenominator_ne_zero (q : XiZeroCopy) (branch : Bool) (w : ℂ)
    (hw : -2 < w.re) : w-2*physicalRate q branch ≠ 0 := by
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  intro he
  have he' := congrArg Complex.re (sub_eq_zero.mp he)
  linarith

/-- The actual cutoff coefficient is square-integrable on both sides of the imaginary axis,
including the original quotient's totalized values at its connection zeros. -/
theorem continuedCutoffRadialCoefficient_band_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) (i : Fin 3) :
    MemLp (continuedCutoffRadialCoefficient q branch w a i) 2 radialMeasure := by
  have hwre : -2 < w.re := (abs_lt.mp hwr).1
  by_cases hc : connection w (principalFrequency q i) = 0
  · let s := physicalRate q branch
    let T := continuedOnset s w
    let J := principalAmplitude q i
    let P : ℝ → ℂ := fun u => (s*(s-1)/4)*(u:ℂ)^(3 : ℕ)*J
    obtain ⟨C,hC,hb⟩ := sourceAmplitude_profile_norm_le_exp s w a T P (by dsimp [P]; fun_prop)
    have hU (t : ℝ) : continuedPrincipalDifference q branch w a i t =
        sourceAmplitude s w a T t*P (radialUnit t) := by
      simp only [continuedPrincipalDifference,continuedTortoiseGreen,continuedResponse,
        continuedHorizonMoment,continuedOuterMoment,hc,neg_zero,div_zero,mul_zero,add_zero,zero_sub]
      dsimp [radialLift,P,s,T,J]
      ring
    have hF : ContinuousOn (continuedCutoffRadialCoefficient q branch w a i) (Iio 0) := by
      intro t ht
      exact (((horizonCoordinate_hasDerivAt t).ofReal_comp).continuousAt.mul
        ((continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i t ht).1.continuousAt)).continuousWithinAt
    apply MemLp.of_le (horizonExponential_memLp (w.re+2) (4*C) (by linarith) (by positivity))
      (hF.aestronglyMeasurable measurableSet_Iio)
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 4*C*Real.exp ((w.re+2)*t))]
    rw [continuedCutoffRadialCoefficient,norm_mul,hU]
    calc
      _ ≤ (4*Real.exp (2*t))*(C*Real.exp (w.re*t)) :=
        mul_le_mul (horizonCoordinate_norm_le_exp t ht) (hb t ht) (norm_nonneg _) (by positivity)
      _ = (4*C)*(Real.exp (2*t)*Real.exp (w.re*t)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  · have hs := physicalSourceDenominator_ne_zero q branch w hwre
    have hD : principalClearingFactor q branch w i ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hs) hc
    have h := (clearedCutoffRadialCoefficient_memLp q branch w a hw hwre hwr i).const_smul
      (principalClearingFactor q branch w i)⁻¹
    apply h.ae_eq
    filter_upwards [] with t
    change (principalClearingFactor q branch w i)⁻¹ * clearedCutoffRadialCoefficient q branch w a i t = _
    rw [clearedCutoffRadialCoefficient_eq q branch w a i hs hc t,← mul_assoc,inv_mul_cancel₀ hD,one_mul]

end
end RHTower.D4BMJointSource
