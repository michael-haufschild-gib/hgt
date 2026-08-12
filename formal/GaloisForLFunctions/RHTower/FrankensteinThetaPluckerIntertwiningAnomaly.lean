import GaloisForLFunctions.RHTower.FrankensteinPluckerXiHilbertAdmission
import GaloisForLFunctions.RHTower.HedenmalmThetaDivisorPolarizedInterpolation

/-!
# Exact theta-to-Pluecker intertwining anomaly

The pinned monopole canonically identifies each one-dimensional theta Xi eigenspace with either
retained physical Pluecker carrier.  This gives coefficient-faithful continuous lifts off the
critical line, without choosing a basis scalar.

The theta divisor vector is killed by its exact source pencil.  The faithful physical Pluecker
operator does not kill its lifted carrier off the critical line.  Therefore literal
intertwining is impossible: its anomaly is exactly the positive Pluecker detector vector.  The
same statement holds for both retained orientations and is odd under critical-line reflection.

This is a sharp obstruction and a producer specification.  Any source correction capable of
closing the Frankenstein route must cancel this explicit vector before bounded scalarization;
source-pencil vanishing alone cannot do so.
-/

open Complex MeasureTheory
open scoped ENNReal InnerProductSpace

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmClosedWeightedDerivative

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

private theorem thetaSource_sqrt_mass_ne_zero_for_plucker_lift :
    (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'

/-! ## Canonical monopole-normalized lifts -/

/-- Canonical continuous lift from the theta source space to the lower retained Pluecker
orientation.  On the Xi eigenspace it preserves the unique pinned-mean coefficient. -/
def frankensteinThetaXiLowerPluckerLift (q : RHTower.XiZeroCopy) :
    ThetaH →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert :=
  ((Real.sqrt thetaSource.mass : ℂ)⁻¹) •
    thetaPinnedMeanCLM.smulRight
      (frankensteinXiLowerPhysicalPluckerHilbertCarrier q)

/-- Canonical continuous lift to the upper retained Pluecker orientation. -/
def frankensteinThetaXiUpperPluckerLift (q : RHTower.XiZeroCopy) :
    ThetaH →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert :=
  ((Real.sqrt thetaSource.mass : ℂ)⁻¹) •
    thetaPinnedMeanCLM.smulRight
      (frankensteinXiUpperPhysicalPluckerHilbertCarrier q)

@[simp] theorem frankensteinThetaXiLowerPluckerLift_apply
    (q : RHTower.XiZeroCopy) (f : ThetaH) :
    frankensteinThetaXiLowerPluckerLift q f =
      (pinnedMean f / (Real.sqrt thetaSource.mass : ℂ)) •
        frankensteinXiLowerPhysicalPluckerHilbertCarrier q := by
  simp only [frankensteinThetaXiLowerPluckerLift, smul_apply,
    ContinuousLinearMap.smulRight_apply, thetaPinnedMeanCLM_apply]
  rw [div_eq_mul_inv]
  module

@[simp] theorem frankensteinThetaXiUpperPluckerLift_apply
    (q : RHTower.XiZeroCopy) (f : ThetaH) :
    frankensteinThetaXiUpperPluckerLift q f =
      (pinnedMean f / (Real.sqrt thetaSource.mass : ℂ)) •
        frankensteinXiUpperPhysicalPluckerHilbertCarrier q := by
  simp only [frankensteinThetaXiUpperPluckerLift, smul_apply,
    ContinuousLinearMap.smulRight_apply, thetaPinnedMeanCLM_apply]
  rw [div_eq_mul_inv]
  module

@[simp] theorem frankensteinThetaXiLowerPluckerLift_eigenvector
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiLowerPluckerLift q
        (RHTower.thetaXiDivisorEigenvector q) =
      frankensteinXiLowerPhysicalPluckerHilbertCarrier q := by
  rw [frankensteinThetaXiLowerPluckerLift_apply,
    pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass,
    div_self thetaSource_sqrt_mass_ne_zero_for_plucker_lift, one_smul]

@[simp] theorem frankensteinThetaXiUpperPluckerLift_eigenvector
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiUpperPluckerLift q
        (RHTower.thetaXiDivisorEigenvector q) =
      frankensteinXiUpperPhysicalPluckerHilbertCarrier q := by
  rw [frankensteinThetaXiUpperPluckerLift_apply,
    pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass,
    div_self thetaSource_sqrt_mass_ne_zero_for_plucker_lift, one_smul]

/-- Off the critical line, the lower lift is coefficient-faithful on the complete divisor
eigenspace, including every analytic-multiplicity copy. -/
theorem frankensteinThetaXiLowerPluckerLift_eq_zero_iff_of_eigen_offline
    (q : RHTower.XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2)
    {f : ThetaH}
    (hf : thetaCompactSourceInverse f =
      RHTower.thetaXiReciprocalEigenvalue q • f) :
    frankensteinThetaXiLowerPluckerLift q f = 0 ↔ f = 0 := by
  have hcarrier : frankensteinXiLowerPhysicalPluckerHilbertCarrier q ≠ 0 :=
    (frankensteinXiLowerPhysicalPluckerHilbertCarrier_eq_zero_iff q).not.mpr hq
  constructor
  · intro hlift
    rw [frankensteinThetaXiLowerPluckerLift_apply] at hlift
    have hratio : pinnedMean f / (Real.sqrt thetaSource.mass : ℂ) = 0 :=
      (smul_eq_zero.mp hlift).resolve_right hcarrier
    have hmean : pinnedMean f = 0 :=
      (div_eq_zero_iff.mp hratio).resolve_right
        thetaSource_sqrt_mass_ne_zero_for_plucker_lift
    rw [thetaCompactSourceInverse_eigenvector_eq_mean_smul_thetaXiDivisorEigenvector q hf,
      hmean, zero_div, zero_smul]
  · rintro rfl
    exact map_zero _

/-- Off the critical line, the upper lift is coefficient-faithful on the same divisor
eigenspace. -/
theorem frankensteinThetaXiUpperPluckerLift_eq_zero_iff_of_eigen_offline
    (q : RHTower.XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2)
    {f : ThetaH}
    (hf : thetaCompactSourceInverse f =
      RHTower.thetaXiReciprocalEigenvalue q • f) :
    frankensteinThetaXiUpperPluckerLift q f = 0 ↔ f = 0 := by
  have hcarrier : frankensteinXiUpperPhysicalPluckerHilbertCarrier q ≠ 0 :=
    (frankensteinXiUpperPhysicalPluckerHilbertCarrier_eq_zero_iff q).not.mpr hq
  constructor
  · intro hlift
    rw [frankensteinThetaXiUpperPluckerLift_apply] at hlift
    have hratio : pinnedMean f / (Real.sqrt thetaSource.mass : ℂ) = 0 :=
      (smul_eq_zero.mp hlift).resolve_right hcarrier
    have hmean : pinnedMean f = 0 :=
      (div_eq_zero_iff.mp hratio).resolve_right
        thetaSource_sqrt_mass_ne_zero_for_plucker_lift
    rw [thetaCompactSourceInverse_eigenvector_eq_mean_smul_thetaXiDivisorEigenvector q hf,
      hmean, zero_div, zero_smul]
  · rintro rfl
    exact map_zero _

/-! ## Exact source pencil and its target anomalies -/

/-- Exact divisor-point source pencil. -/
def frankensteinThetaXiSourcePencilResidual (q : RHTower.XiZeroCopy) :
    ThetaH →L[ℂ] ThetaH :=
  thetaCompactSourceInverse -
    RHTower.thetaXiReciprocalEigenvalue q • ContinuousLinearMap.id ℂ ThetaH

@[simp] theorem frankensteinThetaXiSourcePencilResidual_eigenvector
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiSourcePencilResidual q
        (RHTower.thetaXiDivisorEigenvector q) = 0 := by
  simp [frankensteinThetaXiSourcePencilResidual,
    RHTower.thetaCompactSourceInverse_thetaXi_eigen]

/-- Failure of literal lower theta-to-Pluecker intertwining. -/
def frankensteinThetaXiLowerPluckerIntertwiningAnomaly
    (q : RHTower.XiZeroCopy) :
    ThetaH →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert :=
  gammaSewnCriticalPhysicalPluckerSpectralOperator.comp
      (frankensteinThetaXiLowerPluckerLift q) -
    (frankensteinThetaXiLowerPluckerLift q).comp
      (frankensteinThetaXiSourcePencilResidual q)

/-- Failure of literal upper theta-to-Pluecker intertwining. -/
def frankensteinThetaXiUpperPluckerIntertwiningAnomaly
    (q : RHTower.XiZeroCopy) :
    ThetaH →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert :=
  gammaSewnCriticalPhysicalPluckerSpectralOperator.comp
      (frankensteinThetaXiUpperPluckerLift q) -
    (frankensteinThetaXiUpperPluckerLift q).comp
      (frankensteinThetaXiSourcePencilResidual q)

@[simp] theorem frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
        (RHTower.thetaXiDivisorEigenvector q) =
      gammaSewnCriticalPhysicalPluckerSpectralOperator
        (frankensteinXiLowerPhysicalPluckerHilbertCarrier q) := by
  rw [frankensteinThetaXiLowerPluckerIntertwiningAnomaly, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    frankensteinThetaXiLowerPluckerLift_eigenvector,
    frankensteinThetaXiSourcePencilResidual_eigenvector, map_zero, sub_zero]

@[simp] theorem frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiUpperPluckerIntertwiningAnomaly q
        (RHTower.thetaXiDivisorEigenvector q) =
      gammaSewnCriticalPhysicalPluckerSpectralOperator
        (frankensteinXiUpperPhysicalPluckerHilbertCarrier q) := by
  rw [frankensteinThetaXiUpperPluckerIntertwiningAnomaly, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    frankensteinThetaXiUpperPluckerLift_eigenvector,
    frankensteinThetaXiSourcePencilResidual_eigenvector, map_zero, sub_zero]

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_xiUpper_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    gammaSewnCriticalPhysicalPluckerSpectralOperator
        (frankensteinXiUpperPhysicalPluckerHilbertCarrier q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_eq_zero_iff,
    frankensteinXiUpperPhysicalPluckerHilbertCarrier_eq_zero_iff]

/-- Lower anomaly vanishes exactly on the critical line. -/
theorem frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
        (RHTower.thetaXiDivisorEigenvector q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector,
    gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_xiLower_eq_zero_iff]

/-- Upper anomaly has the same exact zero radical. -/
theorem frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiUpperPluckerIntertwiningAnomaly q
        (RHTower.thetaXiDivisorEigenvector q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector,
    gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_xiUpper_eq_zero_iff]

/-- Literal lower intertwining on the actual divisor mode is itself exactly the critical-line
condition. -/
theorem frankensteinThetaXiLowerPlucker_literal_intertwining_iff
    (q : RHTower.XiZeroCopy) :
    gammaSewnCriticalPhysicalPluckerSpectralOperator
        (frankensteinThetaXiLowerPluckerLift q
          (RHTower.thetaXiDivisorEigenvector q)) =
      frankensteinThetaXiLowerPluckerLift q
        (frankensteinThetaXiSourcePencilResidual q
          (RHTower.thetaXiDivisorEigenvector q)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinThetaXiLowerPluckerLift_eigenvector,
    frankensteinThetaXiSourcePencilResidual_eigenvector, map_zero]
  exact gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_xiLower_eq_zero_iff q

/-- Literal upper intertwining has the identical obstruction. -/
theorem frankensteinThetaXiUpperPlucker_literal_intertwining_iff
    (q : RHTower.XiZeroCopy) :
    gammaSewnCriticalPhysicalPluckerSpectralOperator
        (frankensteinThetaXiUpperPluckerLift q
          (RHTower.thetaXiDivisorEigenvector q)) =
      frankensteinThetaXiUpperPluckerLift q
        (frankensteinThetaXiSourcePencilResidual q
          (RHTower.thetaXiDivisorEigenvector q)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinThetaXiUpperPluckerLift_eigenvector,
    frankensteinThetaXiSourcePencilResidual_eigenvector, map_zero]
  exact gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_xiUpper_eq_zero_iff q

/-! ## Reflection orientation -/

theorem frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector_reflection
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiLowerPluckerIntertwiningAnomaly
        (RHTower.xiZeroCopyLineConjEquiv q)
        (RHTower.thetaXiDivisorEigenvector
          (RHTower.xiZeroCopyLineConjEquiv q)) =
      -frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
        (RHTower.thetaXiDivisorEigenvector q) := by
  rw [frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector,
    frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector,
    frankensteinXiLowerPhysicalPluckerHilbertCarrier_reflection, map_neg]

theorem frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector_reflection
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaXiUpperPluckerIntertwiningAnomaly
        (RHTower.xiZeroCopyLineConjEquiv q)
        (RHTower.thetaXiDivisorEigenvector
          (RHTower.xiZeroCopyLineConjEquiv q)) =
      -frankensteinThetaXiUpperPluckerIntertwiningAnomaly q
        (RHTower.thetaXiDivisorEigenvector q) := by
  rw [frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector,
    frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector,
    frankensteinXiUpperPhysicalPluckerHilbertCarrier_reflection, map_neg]

/-- Both coefficient-faithful target anomalies vanish simultaneously exactly on the critical
line.  No orientation is discarded or averaged. -/
theorem frankensteinThetaXiBothPluckerIntertwiningAnomalies_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    (frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q) = 0 ∧
        frankensteinThetaXiUpperPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q) = 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector_eq_zero_iff,
    frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector_eq_zero_iff,
    and_self]

end

end RHTower.HedenmalmThetaSource
