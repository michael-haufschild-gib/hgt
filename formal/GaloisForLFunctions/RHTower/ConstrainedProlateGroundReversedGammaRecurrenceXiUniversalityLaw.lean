import GaloisForLFunctions.RHTower.ConstrainedProlateGroundFixedGammaWardBudgetXiUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeArchThetaFixedGammaWardBudgetRecurrenceUniversalityLaw

/-!
# Constrained-prolate ground reversed Gamma recurrence and Xi universality

The constrained-prolate ground source is a strictly negative scalar multiple of the first
theta-cusp atom.  Transporting both source and Liouville--Gibbs fixed-Gamma coordinates through
that normalization preserves the exact Ward identity, reverses every positive-order
equipartition recurrence, and retains the exact completed-Xi Fourier realization.
-/

open Complex Real MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace RHTower

noncomputable section

/-- Fixed-Gamma source coordinate with the actual constrained-prolate ground normalization. -/
def constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate (j : ℕ) : ℝ :=
  constrainedProlateGroundHermiteXiScale *
    thetaCuspFirstAtomSourceGammaCoordinate j

/-- Fixed-Gamma Liouville--Gibbs coordinate with the actual constrained-prolate ground
normalization. -/
def constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (m : ℕ) : ℝ :=
  constrainedProlateGroundHermiteXiScale *
    thetaCuspFirstAtomGibbsGammaCoordinate m

/-- The normalized source Gamma coordinate is exactly the corresponding constrained ground
moment. -/
theorem constrainedProlateGroundHermiteFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment
    (j : ℕ) :
    constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate j =
      constrainedProlateGroundHermiteAtomRawEvenMoment j 1 := by
  rw [constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate,
    thetaCuspFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment]
  exact (constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta j 1).symm

/-- The constrained source and Gibbs coordinates retain the exact Liouville--Ward bridge. -/
theorem constrainedProlateGroundHermiteFirstAtom_fixedGamma_liouvilleWardBridge_normalized
    (j : ℕ) :
    constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate (j + 1) =
      8 * Real.pi * (j + 1) *
          constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (2 * j + 1) -
        2 * Real.pi *
          constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (2 * j + 2) := by
  rw [constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate,
    thetaCuspFirstAtom_fixedGamma_liouvilleWardBridge]
  simp only [constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate]
  ring

/-- Negative constrained-ground normalization reverses the sharp fixed-Gamma equipartition
recurrence. -/
theorem constrainedProlateGroundHermiteFirstAtom_fixedGamma_reversedEquipartitionRecurrence
    (k : ℕ) (hk : 0 < k) :
    (k : ℝ) *
        constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k - 1) ≤
      4 * Real.pi *
          constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k + 1) +
        (2 * Real.pi - 5 / 2) *
          constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate k := by
  have hrec := thetaCuspFirstAtom_fixedGamma_equipartitionRecurrence k hk
  have hscaled :=
    mul_le_mul_of_nonpos_left hrec constrainedProlateGroundHermiteXiScale_neg.le
  simp only [constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate]
  convert hscaled using 1
  · rfl
  · ring
  · ring

/-- Rational shadow of the reversed equipartition recurrence. -/
theorem constrainedProlateGroundHermiteFirstAtom_fixedGamma_reversedRationalRecurrence
    (k : ℕ) (hk : 0 < k) :
    (k : ℝ) *
        constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k - 1) ≤
      12 * constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k + 1) := by
  have hrec := thetaCuspFirstAtom_fixedGamma_rationalRecurrence k hk
  have hscaled :=
    mul_le_mul_of_nonpos_left hrec constrainedProlateGroundHermiteXiScale_neg.le
  simp only [constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate]
  convert hscaled using 1
  · rfl
  · ring
  · ring

/-- The half-density upper budget becomes a lower budget in normalized source-Gamma
coordinates. -/
theorem constrainedProlateGroundHermiteFirstAtom_fixedGamma_halfDensityLowerBudget_normalized :
    constrainedProlateGroundHermiteXiScale *
        ((4 * Real.pi - 1) * Real.exp (-Real.pi)) ≤
      constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate 0 +
        constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate 1 / 8 +
          constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate 2 / 384 := by
  rw [constrainedProlateGroundHermiteFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment,
    constrainedProlateGroundHermiteFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment,
    constrainedProlateGroundHermiteFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment]
  exact constrainedProlateGroundHermiteFirstAtom_halfDensityLowerBudget

/-- Joint constrained-prolate certificate: exact source coordinates and Ward bridge, both reversed
fixed-Gamma recurrences, the signed endpoint budget, and the completed-Xi Fourier transform. -/
structure ConstrainedProlateGroundReversedGammaRecurrenceXiCertificate : Prop where
  sourceCoordinate :
    ∀ j : ℕ,
      constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate j =
        constrainedProlateGroundHermiteAtomRawEvenMoment j 1
  wardBridge :
    ∀ j : ℕ,
      constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate (j + 1) =
        8 * Real.pi * (j + 1) *
            constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (2 * j + 1) -
          2 * Real.pi *
            constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (2 * j + 2)
  reversedEquipartitionRecurrence :
    ∀ k : ℕ, 0 < k →
      (k : ℝ) *
          constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k - 1) ≤
        4 * Real.pi *
            constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k + 1) +
          (2 * Real.pi - 5 / 2) *
            constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate k
  reversedRationalRecurrence :
    ∀ k : ℕ, 0 < k →
      (k : ℝ) *
          constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k - 1) ≤
        12 * constrainedProlateGroundHermiteFirstAtomGibbsGammaCoordinate (k + 1)
  halfDensityLowerBudget :
    constrainedProlateGroundHermiteXiScale *
        ((4 * Real.pi - 1) * Real.exp (-Real.pi)) ≤
      constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate 0 +
        constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate 1 / 8 +
          constrainedProlateGroundHermiteFirstAtomSourceGammaCoordinate 2 / 384
  xiFourierRealization :
    ∀ t : ℝ,
      (𝓕 constrainedProlateGroundHermiteSchwartz) (t / (2 * Real.pi)) =
        (constrainedProlateGroundHermiteXiScale : ℂ) * XiC (t : ℂ)

/-- **Constrained-prolate reversed Gamma-recurrence/Xi universality law.**  The negative
normalization converting the theta-cusp source into the constrained-prolate ground state reverses
the whole fixed-Gamma recurrence hierarchy, without changing the exact Ward transport or Xi
Fourier realization. -/
theorem constrainedProlateGround_reversedGammaRecurrenceXiUniversality :
    ConstrainedProlateGroundReversedGammaRecurrenceXiCertificate where
  sourceCoordinate :=
    constrainedProlateGroundHermiteFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment
  wardBridge :=
    constrainedProlateGroundHermiteFirstAtom_fixedGamma_liouvilleWardBridge_normalized
  reversedEquipartitionRecurrence :=
    constrainedProlateGroundHermiteFirstAtom_fixedGamma_reversedEquipartitionRecurrence
  reversedRationalRecurrence :=
    constrainedProlateGroundHermiteFirstAtom_fixedGamma_reversedRationalRecurrence
  halfDensityLowerBudget :=
    constrainedProlateGroundHermiteFirstAtom_fixedGamma_halfDensityLowerBudget_normalized
  xiFourierRealization :=
    fourier_constrainedProlateGroundHermiteSchwartz_scaled

end

end RHTower
