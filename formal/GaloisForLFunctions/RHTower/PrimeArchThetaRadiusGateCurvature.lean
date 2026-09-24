import GaloisForLFunctions.RHTower.PrimeArchThetaRadiusGramGate
import GaloisForLFunctions.RHTower.PrimeArchThetaGateCurvatureIdentity
import GaloisForLFunctions.RHTower.XiPrimeMarkedQuarticEffectiveRank
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Curvature of the radius-mixing gate

The new four-moment determinant gate is quadratic in the fourth theta moment.
Its leading coefficient is strictly negative for the literal source.  Thus a
source-specific interval for that moment can be tested at its endpoints.
-/

namespace RHTower
noncomputable section

theorem radiusMixingGate_curvature_exact (a b c : ℝ) :
    let v := a ^ 2 / 2 - b / 6
    let w := c / 120 - a * b / 8 + a ^ 3 / 4
    let d := a * w - v ^ 2
    let q := a * c - b ^ 2
    let qR := 21 * a * c - 25 * b ^ 2
    let r := a ^ 2 - 18 * v
    243 * d - 11 * qR / 70 =
      -51 * q / 40 + b * (176 * b - 693 * a ^ 2 - 441 * r) / 280 := by
  dsimp only
  ring

/-- Strict downward curvature of the second four-moment determinant gate for
the completed theta source. -/
theorem thetaCusp_radiusMixingGate_curvature_neg :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let d := normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
      normalizedPrimeArchMoment 1 ^ 2
    let qR := 21 * a * c - 25 * b ^ 2
    243 * d - 11 * qR / 70 < 0 := by
  dsimp only
  let a := thetaCuspNormalizedEvenMoment 1
  let b := thetaCuspNormalizedEvenMoment 2
  let c := thetaCuspNormalizedEvenMoment 3
  let v := a ^ 2 / 2 - b / 6
  let w := c / 120 - a * b / 8 + a ^ 3 / 4
  let d := normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
    normalizedPrimeArchMoment 1 ^ 2
  let q := a * c - b ^ 2
  let qR := 21 * a * c - 25 * b ^ 2
  let r := a ^ 2 - 18 * v
  have hm₀ : normalizedPrimeArchMoment 0 = a :=
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment
  have hm₁ : normalizedPrimeArchMoment 1 = v :=
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment
  have hm₂ : normalizedPrimeArchMoment 2 = w :=
    normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment
  have hd : d = a * w - v ^ 2 := by
    dsimp [d]
    rw [hm₀, hm₁, hm₂]
  have hq : 0 < q := thetaCuspNormalizedEvenMoment_shifted_q_pos
  have hb : 0 < b := by
    dsimp [b, thetaCuspNormalizedEvenMoment]
    exact div_pos (thetaCuspRawEvenMoment_pos 2) thetaCuspRawEvenMoment_zero_pos
  have hv : 0 < v := by
    rw [← hm₁]
    exact normalizedPrimeArchMoment_one_pos
  have hrank := routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy
  rw [routeKQuarticHalfEnergy, routeKQuarticHalfMass,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment] at hrank
  have hr : 0 < r := by
    dsimp [r]
    rw [← hm₀, ← hm₁]
    nlinarith
  have hba : b < 3 * a ^ 2 := by
    dsimp [v] at hv
    nlinarith
  have hfactor : 176 * b - 693 * a ^ 2 - 441 * r < 0 := by
    nlinarith [sq_nonneg a]
  have hprod : b * (176 * b - 693 * a ^ 2 - 441 * r) < 0 :=
    mul_neg_of_pos_of_neg hb hfactor
  have hid := radiusMixingGate_curvature_exact a b c
  change 243 * (a * w - v ^ 2) - 11 * qR / 70 =
    -51 * q / 40 + b * (176 * b - 693 * a ^ 2 - 441 * r) / 280 at hid
  change 243 * d - 11 * qR / 70 < 0
  rw [hd, hid]
  nlinarith

end
end RHTower
