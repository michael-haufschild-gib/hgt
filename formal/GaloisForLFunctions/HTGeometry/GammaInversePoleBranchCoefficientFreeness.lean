import GaloisForLFunctions.HTGeometry.GammaPoleAnalyticCoefficientFreeness
import GaloisForLFunctions.HTGeometry.FormalUnitInverseFreeness
import GaloisForLFunctions.HTGeometry.FormalCompositionalInverseFreeness

/-!
# Free coefficients on all normalized inverse-Gamma pole branches

At pole `-n`, write the exact factorially normalized Gamma germ as

`Gamma(-n + s_n X) = -U_n(X) / X`,  `U_n(0)=1`.

The formal coordinate sent by Gamma to the reciprocal coordinate is

`A_n(X)=X/U_n(X)`.

Its tangent-to-identity compositional inverse `B_n` is characterized by

`Gamma(-n + s_n B_n(T)) = -1/T`.

The coefficients of all `U_n` are already algebraically independent as germs in the pole index.
Multiplicative inversion and then compositional inversion are automorphisms of the universal
coefficient algebra, so all nonlinear coefficients of the full inverse-branch family `B_n` remain
countably algebraically independent.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaInversePoleNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- The positive Taylor coefficients of the actual analytic units `U_n`, as pole-index germs. -/
def gammaPoleUnitPositiveCoefficientGerm (j : ℕ) : NatGerm :=
  -actualGammaPoleRegularCoefficientGerm j

theorem gammaPoleUnitPositiveCoefficientGerm_eq_actualTaylorCoefficient (j : ℕ) :
    gammaPoleUnitPositiveCoefficientGerm j =
      (fun N : ℕ =>
        (((j + 1).factorial : ℂ)⁻¹) *
          iteratedDeriv (j + 1) (gammaPoleRegularUnit (N - 1)) 0 : NatGerm) := by
  rw [gammaPoleUnitPositiveCoefficientGerm,
    actualGammaPoleRegularCoefficientGerm]
  rw [← Filter.Germ.coe_neg, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun _N => by simp

theorem algebraicIndependent_gammaPoleUnitPositiveCoefficientGerm :
    AlgebraicIndependent ℂ gammaPoleUnitPositiveCoefficientGerm := by
  exact AlgebraicIndependent.neg
    algebraicIndependent_actualGammaPoleRegularCoefficientGerm

/-- The coefficient-germ Taylor series of the actual analytic unit family `U_n`. -/
def gammaPoleUnitFormalGerm : NatGerm⟦X⟧ :=
  unitPowerSeriesOfCoefficients gammaPoleUnitPositiveCoefficientGerm

/-- The formal reciprocal `1/U_n`, uniformly across the pole family. -/
def gammaPoleReciprocalUnitFormalGerm : NatGerm⟦X⟧ :=
  unitInversePowerSeriesOfCoefficients gammaPoleUnitPositiveCoefficientGerm

def gammaPoleReciprocalUnitCoefficientGerm (j : ℕ) : NatGerm :=
  unitInverseCoefficientOfCoefficients gammaPoleUnitPositiveCoefficientGerm j

theorem algebraicIndependent_gammaPoleReciprocalUnitCoefficientGerm :
    AlgebraicIndependent ℂ gammaPoleReciprocalUnitCoefficientGerm := by
  exact AlgebraicIndependent.unitInverseCoefficientOfCoefficients
    algebraicIndependent_gammaPoleUnitPositiveCoefficientGerm

/-- The direct normalized Gamma coordinate `A_n(X)=X/U_n(X)`. -/
def gammaPoleDirectCoordinateFormalGerm : NatGerm⟦X⟧ :=
  tangentPowerSeriesOfCoefficients gammaPoleReciprocalUnitCoefficientGerm

theorem gammaPoleDirectCoordinateFormalGerm_eq :
    gammaPoleDirectCoordinateFormalGerm =
      PowerSeries.X * gammaPoleReciprocalUnitFormalGerm := by
  apply PowerSeries.ext
  intro n
  obtain (_ | n) := n
  · simp [gammaPoleDirectCoordinateFormalGerm]
  · obtain (_ | n) := n
    · simp [gammaPoleDirectCoordinateFormalGerm,
        gammaPoleReciprocalUnitFormalGerm]
    · rw [gammaPoleDirectCoordinateFormalGerm,
        PowerSeries.coeff_succ_X_mul,
        show n + 1 + 1 = n + 2 by omega,
        tangentPowerSeriesOfCoefficients_coeff_add_two]
      rfl

theorem gammaPoleDirectCoordinateFormalGerm_mul_unit :
    gammaPoleDirectCoordinateFormalGerm * gammaPoleUnitFormalGerm = PowerSeries.X := by
  rw [gammaPoleDirectCoordinateFormalGerm_eq, mul_assoc]
  change PowerSeries.X *
      (unitInversePowerSeriesOfCoefficients gammaPoleUnitPositiveCoefficientGerm *
        unitPowerSeriesOfCoefficients gammaPoleUnitPositiveCoefficientGerm) = PowerSeries.X
  rw [unitInverse_mul_unitPowerSeries, mul_one]

/-- The normalized inverse branch at every Gamma pole. -/
def gammaInversePoleBranchFormalGerm : NatGerm⟦X⟧ :=
  tangentInversePowerSeriesOfCoefficients gammaPoleReciprocalUnitCoefficientGerm

/-- Its complete nonlinear coefficient family. -/
def gammaInversePoleBranchCoefficientGerm (j : ℕ) : NatGerm :=
  tangentInverseCoefficientOfCoefficients gammaPoleReciprocalUnitCoefficientGerm j

/-- **Inverse-Gamma pole-branch coefficient freeness.**  The complete nonlinear coefficient
family of all normalized inverse branches at the negative-integer Gamma poles is countably
algebraically independent over `ℂ`. -/
theorem algebraicIndependent_gammaInversePoleBranchCoefficientGerm :
    AlgebraicIndependent ℂ gammaInversePoleBranchCoefficientGerm := by
  exact AlgebraicIndependent.tangentInverseCoefficientOfCoefficients
    algebraicIndependent_gammaPoleReciprocalUnitCoefficientGerm

theorem gammaPoleDirectCoordinate_subst_inverseBranch :
    gammaPoleDirectCoordinateFormalGerm.subst gammaInversePoleBranchFormalGerm =
      PowerSeries.X := by
  exact tangentPowerSeries_subst_tangentInverse gammaPoleReciprocalUnitCoefficientGerm

theorem gammaInversePoleBranch_subst_directCoordinate :
    gammaInversePoleBranchFormalGerm.subst gammaPoleDirectCoordinateFormalGerm =
      PowerSeries.X := by
  exact tangentInverse_subst_tangentPowerSeries gammaPoleReciprocalUnitCoefficientGerm

/-- Division-free inverse-Gamma branch equation `B(T)=T U(B(T))`. -/
theorem gammaInversePoleBranch_eq_X_mul_subst_unit :
    gammaInversePoleBranchFormalGerm =
      PowerSeries.X *
        gammaPoleUnitFormalGerm.subst gammaInversePoleBranchFormalGerm := by
  let hB : PowerSeries.HasSubst gammaInversePoleBranchFormalGerm :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (tangentInversePowerSeriesOfCoefficients_constantCoeff
        gammaPoleReciprocalUnitCoefficientGerm)
  have hrecip :
      gammaPoleReciprocalUnitFormalGerm.subst gammaInversePoleBranchFormalGerm *
        gammaPoleUnitFormalGerm.subst gammaInversePoleBranchFormalGerm = 1 := by
    have h := congrArg
      (fun F : NatGerm⟦X⟧ => F.subst gammaInversePoleBranchFormalGerm)
      (unitInverse_mul_unitPowerSeries gammaPoleUnitPositiveCoefficientGerm)
    have h' :
        gammaPoleReciprocalUnitFormalGerm.subst gammaInversePoleBranchFormalGerm *
          gammaPoleUnitFormalGerm.subst gammaInversePoleBranchFormalGerm =
            (1 : NatGerm⟦X⟧).subst gammaInversePoleBranchFormalGerm := by
      simpa [gammaPoleReciprocalUnitFormalGerm, gammaPoleUnitFormalGerm,
        PowerSeries.subst_mul hB] using h
    have hone :
        (1 : NatGerm⟦X⟧).subst gammaInversePoleBranchFormalGerm = 1 := by
      rw [← PowerSeries.coe_substAlgHom hB]
      exact map_one _
    exact h'.trans hone
  have hdirect :
      gammaInversePoleBranchFormalGerm *
        gammaPoleReciprocalUnitFormalGerm.subst gammaInversePoleBranchFormalGerm =
          PowerSeries.X := by
    have h := gammaPoleDirectCoordinate_subst_inverseBranch
    rw [gammaPoleDirectCoordinateFormalGerm_eq] at h
    simpa [PowerSeries.subst_mul hB, PowerSeries.subst_X hB] using h
  calc
    gammaInversePoleBranchFormalGerm = gammaInversePoleBranchFormalGerm * 1 := by
      rw [mul_one]
    _ = gammaInversePoleBranchFormalGerm *
        (gammaPoleReciprocalUnitFormalGerm.subst gammaInversePoleBranchFormalGerm *
          gammaPoleUnitFormalGerm.subst gammaInversePoleBranchFormalGerm) := by
      rw [hrecip]
    _ = (gammaInversePoleBranchFormalGerm *
        gammaPoleReciprocalUnitFormalGerm.subst gammaInversePoleBranchFormalGerm) *
          gammaPoleUnitFormalGerm.subst gammaInversePoleBranchFormalGerm := by
      rw [mul_assoc]
    _ = PowerSeries.X *
        gammaPoleUnitFormalGerm.subst gammaInversePoleBranchFormalGerm := by
      rw [hdirect]

end

end GaloisForLFunctions
