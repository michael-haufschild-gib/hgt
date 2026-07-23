import GaloisForLFunctions.RHTower.ConstrainedProlateApertureXiMetric
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomGammaIntegral
import GaloisForLFunctions.RHTower.PrimeArchThetaHalfDensityMomentRemainder
import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsGammaCoordinate
import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard

/-!
# Constrained-prolate ground fixed-Gamma Ward/budget/Xi universality

The exact negative theta normalization of the limiting constrained ground source transports its
fixed-Gamma moment hierarchy, Liouville--Ward bridge, and half-density budget while the global
Fourier transform remains the same normalization of completed Xi.
-/

open Complex Real MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace RHTower

noncomputable section

/-- Even raw moment of one integer atom of the limiting constrained ground Hermite source. -/
def constrainedProlateGroundHermiteAtomRawEvenMoment (j n : ℕ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * constrainedProlateGroundHermiteSourceTerm x n

/-- Every constrained ground atom moment is the exact normalized theta atom moment. -/
theorem constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta
    (j n : ℕ) :
    constrainedProlateGroundHermiteAtomRawEvenMoment j n =
      constrainedProlateGroundHermiteXiScale *
        thetaCuspAtomRawEvenMoment j n := by
  rw [constrainedProlateGroundHermiteAtomRawEvenMoment,
    thetaCuspAtomRawEvenMoment]
  rw [show
      (fun x : ℝ =>
        x ^ (2 * j) * constrainedProlateGroundHermiteSourceTerm x n) =
        fun x : ℝ => constrainedProlateGroundHermiteXiScale *
          (x ^ (2 * j) * thetaCuspSourceTerm x n) by
      funext x
      rw [constrainedProlateGroundHermiteSourceTerm_eq]
      ring]
  rw [integral_const_mul]
  ring

/-- The constrained ground normalization is strictly negative. -/
theorem constrainedProlateGroundHermiteXiScale_neg :
    constrainedProlateGroundHermiteXiScale < 0 := by
  unfold constrainedProlateGroundHermiteXiScale
  apply neg_lt_zero.mpr
  exact div_pos (by positivity) (by positivity)

/-- Every dominant constrained ground moment has an exact fixed-half-line Gamma coordinate. -/
theorem constrainedProlateGroundHermiteFirstAtomRawEvenMoment_eq_gammaIntegral
    (j : ℕ) :
    constrainedProlateGroundHermiteAtomRawEvenMoment j 1 =
      constrainedProlateGroundHermiteXiScale *
        ((2 * Real.pi / (4 : ℝ) ^ j) *
          ∫ t : ℝ in Ioi 1, thetaCuspFirstAtomGammaIntegrand j t) := by
  rw [constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta,
    thetaCuspAtomRawEvenMoment_one_eq_gammaIntegral]

/-- Positive even constrained moments obey the exact Ward bridge to consecutive Gibbs
log-Gamma coordinates. -/
theorem constrainedProlateGroundHermiteFirstAtom_fixedGamma_liouvilleWardBridge
    (j : ℕ) :
    constrainedProlateGroundHermiteAtomRawEvenMoment (j + 1) 1 =
      constrainedProlateGroundHermiteXiScale *
        (8 * Real.pi * (j + 1) *
            ((1 / (2 : ℝ) ^ ((2 * j + 1) + 1)) *
              ∫ t : ℝ in Ioi 1,
                thetaCuspFirstAtomSingleGibbsGammaIntegrand (2 * j + 1) t) -
          2 * Real.pi *
            ((1 / (2 : ℝ) ^ ((2 * j + 2) + 1)) *
              ∫ t : ℝ in Ioi 1,
                thetaCuspFirstAtomSingleGibbsGammaIntegrand (2 * j + 2) t)) := by
  rw [constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta,
    thetaCuspAtomRawEvenMoment_succ_eq_liouvilleGibbs j (by norm_num),
    thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral,
    thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral]

/-- Negative source normalization reverses the theta half-density upper budget into a lower
budget for the first three constrained ground moments. -/
theorem constrainedProlateGroundHermiteFirstAtom_halfDensityLowerBudget :
    constrainedProlateGroundHermiteXiScale *
        ((4 * Real.pi - 1) * Real.exp (-Real.pi)) ≤
      constrainedProlateGroundHermiteAtomRawEvenMoment 0 1 +
        constrainedProlateGroundHermiteAtomRawEvenMoment 1 1 / 8 +
          constrainedProlateGroundHermiteAtomRawEvenMoment 2 1 / 384 := by
  have hscaled :=
    mul_le_mul_of_nonpos_left
      thetaCuspFirstAtomMomentTriple_le_halfDensityBudget
      constrainedProlateGroundHermiteXiScale_neg.le
  rw [constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta,
    constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta,
    constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta]
  calc
    constrainedProlateGroundHermiteXiScale *
          ((4 * Real.pi - 1) * Real.exp (-Real.pi)) ≤
        constrainedProlateGroundHermiteXiScale *
          (thetaCuspAtomRawEvenMoment 0 1 +
            thetaCuspAtomRawEvenMoment 1 1 / 8 +
              thetaCuspAtomRawEvenMoment 2 1 / 384) := hscaled
    _ = constrainedProlateGroundHermiteXiScale *
          thetaCuspAtomRawEvenMoment 0 1 +
        constrainedProlateGroundHermiteXiScale *
          thetaCuspAtomRawEvenMoment 1 1 / 8 +
        constrainedProlateGroundHermiteXiScale *
          thetaCuspAtomRawEvenMoment 2 1 / 384 := by ring

/-- **Constrained-prolate fixed-Gamma Ward/budget/Xi universality law.** The local all-order
moment hierarchy and signed endpoint budget coexist with the exact global Xi transform. -/
theorem constrainedProlateGround_fixedGammaWardBudgetXiUniversality :
    (∀ j : ℕ,
      constrainedProlateGroundHermiteAtomRawEvenMoment j 1 =
        constrainedProlateGroundHermiteXiScale *
          ((2 * Real.pi / (4 : ℝ) ^ j) *
            ∫ t : ℝ in Ioi 1, thetaCuspFirstAtomGammaIntegrand j t)) ∧
    (∀ j : ℕ,
      constrainedProlateGroundHermiteAtomRawEvenMoment (j + 1) 1 =
        constrainedProlateGroundHermiteXiScale *
          (8 * Real.pi * (j + 1) *
              ((1 / (2 : ℝ) ^ ((2 * j + 1) + 1)) *
                ∫ t : ℝ in Ioi 1,
                  thetaCuspFirstAtomSingleGibbsGammaIntegrand (2 * j + 1) t) -
            2 * Real.pi *
              ((1 / (2 : ℝ) ^ ((2 * j + 2) + 1)) *
                ∫ t : ℝ in Ioi 1,
                  thetaCuspFirstAtomSingleGibbsGammaIntegrand (2 * j + 2) t))) ∧
    constrainedProlateGroundHermiteXiScale *
        ((4 * Real.pi - 1) * Real.exp (-Real.pi)) ≤
      constrainedProlateGroundHermiteAtomRawEvenMoment 0 1 +
        constrainedProlateGroundHermiteAtomRawEvenMoment 1 1 / 8 +
          constrainedProlateGroundHermiteAtomRawEvenMoment 2 1 / 384 ∧
    ∀ t : ℝ,
      (𝓕 constrainedProlateGroundHermiteSchwartz) (t / (2 * Real.pi)) =
        (constrainedProlateGroundHermiteXiScale : ℂ) * XiC (t : ℂ) := by
  exact ⟨constrainedProlateGroundHermiteFirstAtomRawEvenMoment_eq_gammaIntegral,
    constrainedProlateGroundHermiteFirstAtom_fixedGamma_liouvilleWardBridge,
    constrainedProlateGroundHermiteFirstAtom_halfDensityLowerBudget,
    fourier_constrainedProlateGroundHermiteSchwartz_scaled⟩

end

end RHTower
