import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCutoffMismatchMellin
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePhysicalPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalSourceCoefficient

/-! Exact evaluation of the complete physical angular source after all three native cutoff corrections are assembled. -/
open Complex Set MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem principal_weyl_values (q : XiZeroCopy) :
    weylCoefficient q false = reflectedCompletedLambda (2*(q.1:ℂ)-1) ∧
    weylCoefficient q true = reflectedCompletedLambda (2*(q.1:ℂ)) := by
  simp only [weylCoefficient,d4BMCompletedEisensteinCuspConstantCoefficient,
    D4BMGlobalAngularResponse.center,Bool.false_eq_true,↓reduceIte]
  constructor <;> congr 1 <;> ring

/-- Reordering the same three principal powers identifies their full sum with the native moment. -/
theorem principalMellin_sum_eq_native (q : XiZeroCopy) (v : ℂ) :
    (∑ i : Fin 3, principalAmplitude q i*nativeCutoffMellinContinuation (v+principalExponent q i)) =
      nativePrincipalMomentContinuation q v := by
  obtain ⟨hm,hp⟩ := principal_weyl_values q
  simp [nativePrincipalMomentContinuation,Fin.sum_univ_three,principalAmplitude,principalExponent,
    nativePrincipalPowerCoefficient,nativePrincipalPowerExponent,hm,hp]
  ring

/-- The three actual cutoff quotients reproduce exactly the reflected correction in the physical residual period. -/
theorem physicalPrincipalCorrection_eq_nativeMoment (q : XiZeroCopy) :
    (∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*
      principalAmplitude q i/physicalAngularGap q q i) =
      reflectedCompletedLambda ((q.1:ℂ)-1)*nativePrincipalMomentContinuation q (-((q.1:ℂ)/2)) := by
  have he (i : Fin 3) : scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*
      principalAmplitude q i/physicalAngularGap q q i =
      reflectedCompletedLambda ((q.1:ℂ)-1)*(principalAmplitude q i*
        nativeCutoffMellinContinuation (-((q.1:ℂ)/2)+principalExponent q i)) := by
    calc
      _ = (scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/physicalAngularGap q q i)*
          principalAmplitude q i := by ring
      _ = _ := by
        rw [physicalScalar_principalCutoff_div_gap,
          show principalExponent q i-(q.1:ℂ)/2=-((q.1:ℂ)/2)+principalExponent q i by ring]
        ring
  simp_rw [he]
  rw [← Finset.mul_sum,principalMellin_sum_eq_native]

/-- The actual complete angular source equals the four-Lambda product; the cutoff terms cancel only after exact assembly. -/
theorem physicalSelfSourceCoefficient_fourLambda (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re) :
    physicalSelfSourceCoefficient q =
      (reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^2*
        reflectedCompletedLambda (1-3*(q.1:ℂ)/2))/2 := by
  rw [physicalSelfSourceCoefficient,physicalPrincipalCorrection_eq_nativeMoment,
    physicalAngularParameter_eq,scalarResidualPeriod_physical_value q hq]
  ring

/-- The remaining angular cancellation is exactly a zero of one of the three displayed native completion factors. -/
theorem physicalSelfSourceCoefficient_zero_iff_Lambda (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re) :
    physicalSelfSourceCoefficient q = 0 ↔
      reflectedCompletedLambda (5*(q.1:ℂ)/2-1) = 0 ∨
      reflectedCompletedLambda ((q.1:ℂ)/2) = 0 ∨
      reflectedCompletedLambda (1-3*(q.1:ℂ)/2) = 0 := by
  rw [physicalSelfSourceCoefficient_fourLambda q hq]
  simp only [div_eq_zero_iff,mul_eq_zero,pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)]
  norm_num [or_assoc]

end
end RHTower.D4BMJointSource
