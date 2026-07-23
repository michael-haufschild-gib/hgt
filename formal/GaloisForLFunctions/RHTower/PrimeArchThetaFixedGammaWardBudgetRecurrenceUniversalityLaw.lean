import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomGammaIntegral
import GaloisForLFunctions.RHTower.PrimeArchThetaHalfDensityMomentRemainder
import GaloisForLFunctions.RHTower.PrimeArchThetaGibbsEquipartition

/-!
# Fixed-Gamma Ward, budget, and recurrence universality

The dominant theta source and its first Liouville--Gibbs atom become one constrained hierarchy
after the common substitution `t = exp (2x)`: the Liouville--Ward bridge, half-density budget,
and every positive-order equipartition recurrence all hold in the same fixed incomplete-Gamma
coordinate.
-/

open Real MeasureTheory Set

noncomputable section

namespace RHTower

/-- Normalized fixed-half-line Gamma coordinate of the dominant theta source moment. -/
def thetaCuspFirstAtomSourceGammaCoordinate (j : ℕ) : ℝ :=
  (2 * Real.pi / (4 : ℝ) ^ j) *
    ∫ t : ℝ in Ioi 1, thetaCuspFirstAtomGammaIntegrand j t

/-- Normalized fixed-half-line Gamma coordinate of the first Liouville--Gibbs moment. -/
def thetaCuspFirstAtomGibbsGammaCoordinate (m : ℕ) : ℝ :=
  (1 / (2 : ℝ) ^ (m + 1)) *
    ∫ t : ℝ in Ioi 1, thetaCuspFirstAtomSingleGibbsGammaIntegrand m t

/-- The source Gamma coordinate is exactly the corresponding first-atom raw even moment. -/
theorem thetaCuspFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment (j : ℕ) :
    thetaCuspFirstAtomSourceGammaCoordinate j =
      thetaCuspAtomRawEvenMoment j 1 := by
  exact (thetaCuspAtomRawEvenMoment_one_eq_gammaIntegral j).symm

/-- The Gibbs Gamma coordinate is exactly the corresponding first-atom Gibbs moment. -/
theorem thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment (m : ℕ) :
    thetaCuspFirstAtomGibbsGammaCoordinate m =
      thetaCuspLiouvilleGibbsMoment m 1 := by
  exact (thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral m).symm

/-- All positive even source Gamma coordinates obey the exact Liouville--Ward bridge to two
consecutive Gibbs Gamma coordinates. -/
theorem thetaCuspFirstAtom_fixedGamma_liouvilleWardBridge (j : ℕ) :
    thetaCuspFirstAtomSourceGammaCoordinate (j + 1) =
      8 * Real.pi * (j + 1) *
          thetaCuspFirstAtomGibbsGammaCoordinate (2 * j + 1) -
        2 * Real.pi * thetaCuspFirstAtomGibbsGammaCoordinate (2 * j + 2) := by
  rw [thetaCuspFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment,
    thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment,
    thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment]
  exact thetaCuspAtomRawEvenMoment_succ_eq_liouvilleGibbs j (by norm_num)

/-- The exact half-density observation bounds the first three source Gamma coordinates. -/
theorem thetaCuspFirstAtom_fixedGamma_halfDensityBudget :
    thetaCuspFirstAtomSourceGammaCoordinate 0 +
        thetaCuspFirstAtomSourceGammaCoordinate 1 / 8 +
          thetaCuspFirstAtomSourceGammaCoordinate 2 / 384 ≤
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
  rw [thetaCuspFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment,
    thetaCuspFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment,
    thetaCuspFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment]
  exact thetaCuspFirstAtomMomentTriple_le_halfDensityBudget

/-- Every positive-order Gibbs Gamma coordinate obeys the sharp first-atom equipartition
recurrence. -/
theorem thetaCuspFirstAtom_fixedGamma_equipartitionRecurrence
    (k : ℕ) (hk : 0 < k) :
    4 * Real.pi * thetaCuspFirstAtomGibbsGammaCoordinate (k + 1) +
        (2 * Real.pi - 5 / 2) * thetaCuspFirstAtomGibbsGammaCoordinate k ≤
      (k : ℝ) * thetaCuspFirstAtomGibbsGammaCoordinate (k - 1) := by
  rw [thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment,
    thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment,
    thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment]
  exact thetaCuspFirstAtomLiouvilleGibbsMoment_succ_equipartition_upper k hk

/-- Rational universal consequence of the Gamma-coordinate equipartition recurrence. -/
theorem thetaCuspFirstAtom_fixedGamma_rationalRecurrence
    (k : ℕ) (hk : 0 < k) :
    12 * thetaCuspFirstAtomGibbsGammaCoordinate (k + 1) ≤
      (k : ℝ) * thetaCuspFirstAtomGibbsGammaCoordinate (k - 1) := by
  rw [thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment,
    thetaCuspFirstAtom_gibbsGammaCoordinate_eq_gibbsMoment]
  exact twelve_mul_thetaCuspFirstAtomLiouvilleGibbsMoment_succ_le k hk

/-- Joint certificate that the dominant source and Gibbs incomplete-Gamma coordinates form one
Ward-constrained, budgeted, recursively controlled hierarchy. -/
structure PrimeArchThetaFixedGammaWardBudgetRecurrenceCertificate : Prop where
  wardBridge :
    ∀ j : ℕ,
      thetaCuspFirstAtomSourceGammaCoordinate (j + 1) =
        8 * Real.pi * (j + 1) *
            thetaCuspFirstAtomGibbsGammaCoordinate (2 * j + 1) -
          2 * Real.pi * thetaCuspFirstAtomGibbsGammaCoordinate (2 * j + 2)
  halfDensityBudget :
    thetaCuspFirstAtomSourceGammaCoordinate 0 +
          thetaCuspFirstAtomSourceGammaCoordinate 1 / 8 +
            thetaCuspFirstAtomSourceGammaCoordinate 2 / 384 ≤
        (4 * Real.pi - 1) * Real.exp (-Real.pi)
  equipartitionRecurrence :
    ∀ k : ℕ, 0 < k →
      4 * Real.pi * thetaCuspFirstAtomGibbsGammaCoordinate (k + 1) +
          (2 * Real.pi - 5 / 2) * thetaCuspFirstAtomGibbsGammaCoordinate k ≤
        (k : ℝ) * thetaCuspFirstAtomGibbsGammaCoordinate (k - 1)
  rationalRecurrence :
    ∀ k : ℕ, 0 < k →
      12 * thetaCuspFirstAtomGibbsGammaCoordinate (k + 1) ≤
        (k : ℝ) * thetaCuspFirstAtomGibbsGammaCoordinate (k - 1)

/-- **Fixed-Gamma Ward/budget/recurrence universality law.** All four constraints hold
simultaneously and without a numerical enclosure. -/
theorem primeArchTheta_fixedGammaWardBudgetRecurrenceUniversality :
    PrimeArchThetaFixedGammaWardBudgetRecurrenceCertificate where
  wardBridge := thetaCuspFirstAtom_fixedGamma_liouvilleWardBridge
  halfDensityBudget := thetaCuspFirstAtom_fixedGamma_halfDensityBudget
  equipartitionRecurrence := thetaCuspFirstAtom_fixedGamma_equipartitionRecurrence
  rationalRecurrence := thetaCuspFirstAtom_fixedGamma_rationalRecurrence

end RHTower
