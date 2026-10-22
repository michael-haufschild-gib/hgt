import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCutoffBulkMellinValue
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalSelfAngularGaps
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeLambdaMeromorphy

/-! The physical principal-cutoff quotient equals the original Mellin moment, with its exact eigenvalue mismatch. -/
open Complex Set MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original boundary term and full bulk term combine into the exact eigenvalue-mismatch factor. -/
theorem cutoffPowerMoment_eq_gap_mul_nativeMellin (delta k : ℂ) (hv : delta+k-1 ≠ 0) :
    cutoffPowerMoment delta k = (k*(k-1)-delta*(delta-1))*nativeCutoffMellinContinuation (delta+k-1) := by
  rw [cutoffPowerMoment_eq,cutoffBulkMoment_eq_nativeMellin delta k hv]
  field_simp [hv]
  ring

/-- The physical same-copy angular gap is the original two-indicial-root factorization. -/
theorem physicalAngularGap_self_indicial (q : XiZeroCopy) (i : Fin 3) :
    physicalAngularGap q q i =
      (principalExponent q i-(1-(q.1:ℂ)/2))*(principalExponent q i-(q.1:ℂ)/2) := by
  unfold physicalAngularGap physicalRadialFrequency
  rw [physicalAngularParameter_eq,mul_pow,neg_sq,Complex.I_sq]
  ring

theorem physicalPrincipal_mellinExponent_ne_zero (q : XiZeroCopy) (i : Fin 3) :
    principalExponent q i-(q.1:ℂ)/2 ≠ 0 := by
  have h := physicalAngularGap_self_ne_zero q i
  rw [physicalAngularGap_self_indicial] at h
  exact (mul_ne_zero_iff.mp h).2

/-- Each actual physical cutoff retains exactly its nonzero Weyl coefficient and complete native moment. -/
theorem physicalScalar_principalCutoff_eq_gap_moment (q : XiZeroCopy) (i : Fin 3) :
    scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) =
      reflectedCompletedLambda ((q.1:ℂ)-1)*physicalAngularGap q q i*
        nativeCutoffMellinContinuation (principalExponent q i-(q.1:ℂ)/2) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (physicalAngularParameter q) false = 1-(q.1:ℂ)/2 := by
    rw [physicalAngularParameter_eq]
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign]
    ring
  have hcm : d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) false =
      reflectedCompletedLambda ((q.1:ℂ)-1) := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,Bool.false_eq_true,↓reduceIte]
    congr 1
    ring
  have hcp : d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) true = 0 := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,↓reduceIte]
    rw [show 1+2*(((q.1:ℂ)-1)/2)=(q.1:ℂ) by ring,nativeCompletedLambda_at_xi]
  have hv : (1-(q.1:ℂ)/2)+principalExponent q i-1 ≠ 0 := by
    rw [show (1-(q.1:ℂ)/2)+principalExponent q i-1=principalExponent q i-(q.1:ℂ)/2 by ring]
    exact physicalPrincipal_mellinExponent_ne_zero q i
  rw [scalarCutoffPeriod_eq_moments,hcm,hcp,hm,zero_mul,add_zero,
    cutoffPowerMoment_eq_gap_mul_nativeMellin _ _ hv]
  rw [physicalAngularGap_self_indicial,
    show (1-(q.1:ℂ)/2)+principalExponent q i-1=principalExponent q i-(q.1:ℂ)/2 by ring]
  ring

/-- Dividing by the derived nonzero angular gap leaves the actual reflected Mellin correction. -/
theorem physicalScalar_principalCutoff_div_gap (q : XiZeroCopy) (i : Fin 3) :
    scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/physicalAngularGap q q i =
      reflectedCompletedLambda ((q.1:ℂ)-1)*nativeCutoffMellinContinuation (principalExponent q i-(q.1:ℂ)/2) := by
  rw [physicalScalar_principalCutoff_eq_gap_moment]
  field_simp [physicalAngularGap_self_ne_zero q i]

end
end RHTower.D4BMJointSource
