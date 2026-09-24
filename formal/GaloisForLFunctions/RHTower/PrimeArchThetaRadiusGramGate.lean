import GaloisForLFunctions.HTGeometry.RadiusShiftedGramAlgebra
import GaloisForLFunctions.RHTower.PrimeArchThetaRadiusShiftedGram
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.ThetaGibbsSteinSourceMinor
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex
import GaloisForLFunctions.RHTower.PrimeArchThetaShiftedGramGate

/-!
# The source's radius-mixing fifth-moment gate

The first-atom Stein inequality makes the radius-mixing shifted size-two
minor strictly positive.  Minimizing the new quadratic form then gives a
second source-specific lower bound for the fifth normalized theta moment.
-/

namespace RHTower
noncomputable section

theorem thetaCusp_radiusMixing_shifted_q_pos :
    0 < 21 * thetaCuspNormalizedEvenMoment 1 *
        thetaCuspNormalizedEvenMoment 3 -
      25 * thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ) := by
  have hward := thetaCuspFirstAtomWardMoment_stein_ratio_bounds.1
  have hfirst :
      14 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ^ (2 : ℕ) ≤
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1 := by
    rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 3]
    have hscaled := mul_le_mul_of_nonneg_left hward
      (sq_nonneg (2 * Real.pi))
    convert hscaled using 1 <;> first | ring | rfl
  have hupper := thetaCuspUpperAdjacentRatioSeparation_of_first_atom hfirst
  rw [ThetaCuspUpperAdjacentRatioSeparation] at hupper
  have hb : 0 < thetaCuspRawEvenMoment 2 := thetaCuspRawEvenMoment_pos 2
  have hqraw : 0 <
      21 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
        25 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hb]
  have hmass : 0 < thetaCuspRawEvenMoment 0 := thetaCuspRawEvenMoment_zero_pos
  change 0 <
    21 * (thetaCuspRawEvenMoment 1 / thetaCuspRawEvenMoment 0) *
        (thetaCuspRawEvenMoment 3 / thetaCuspRawEvenMoment 0) -
      25 * (thetaCuspRawEvenMoment 2 / thetaCuspRawEvenMoment 0) ^ (2 : ℕ)
  have heq :
      21 * (thetaCuspRawEvenMoment 1 / thetaCuspRawEvenMoment 0) *
          (thetaCuspRawEvenMoment 3 / thetaCuspRawEvenMoment 0) -
        25 * (thetaCuspRawEvenMoment 2 / thetaCuspRawEvenMoment 0) ^ (2 : ℕ) =
      (21 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
        25 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) /
        thetaCuspRawEvenMoment 0 ^ (2 : ℕ) := by
    field_simp [hmass.ne']
  rw [heq]
  exact div_pos hqraw (pow_pos hmass 2)

/-- A second unconditional four-moment lower bound on the literal fifth
theta moment, obtained from the positive radius-mixing Gram cone. -/
theorem thetaCusp_radiusMixing_fifthMoment_gate :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let f := thetaCuspNormalizedEvenMoment 5
    0 ≤ 11 * (21 * a * c - 25 * b ^ (2 : ℕ)) * f -
      (243 * a * e ^ (2 : ℕ) - 630 * b * c * e + 343 * c ^ (3 : ℕ)) := by
  dsimp only
  exact GaloisForLFunctions.HTGeometry.radiusQuadratic_nonneg_implies_shiftedGram
    _ _ _ _ _ thetaCusp_radiusMixing_shifted_q_pos
    thetaCuspNormalizedEvenMoment_radiusQuadratic_nonneg

/-- The first open prime--archimedean determinant is bounded below by the
radius-mixing four-moment gate. This is a different source-specific test from
the ordinary shifted theta Gram gate. -/
theorem primeArch_three_det_radiusMixingGate_lower :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let m₀ := normalizedPrimeArchMoment 0
    let m₁ := normalizedPrimeArchMoment 1
    let m₂ := normalizedPrimeArchMoment 2
    let m₃ := normalizedPrimeArchMoment 3
    let qR := 21 * a * c - 25 * b ^ (2 : ℕ)
    let pR := 243 * a * e ^ (2 : ℕ) - 630 * b * c * e + 343 * c ^ (3 : ℕ)
    let d := m₀ * m₂ - m₁ ^ (2 : ℕ)
    let B := 9 * m₀ * e - 504 * m₁ * c + 15120 * m₂ * b - 181440 * m₃ * a
    let C := m₀ * m₃ ^ (2 : ℕ) - 2 * m₁ * m₂ * m₃ + m₂ ^ (3 : ℕ)
    d * pR - 11 * qR * (d * B + 362880 * C) ≤
      362880 * 11 * qR * (primeArchSourceMomentHankelMatrix 3).det := by
  dsimp only
  let a := thetaCuspNormalizedEvenMoment 1
  let b := thetaCuspNormalizedEvenMoment 2
  let c := thetaCuspNormalizedEvenMoment 3
  let e := thetaCuspNormalizedEvenMoment 4
  let f := thetaCuspNormalizedEvenMoment 5
  let m₀ := normalizedPrimeArchMoment 0
  let m₁ := normalizedPrimeArchMoment 1
  let m₂ := normalizedPrimeArchMoment 2
  let m₃ := normalizedPrimeArchMoment 3
  let qR := 21 * a * c - 25 * b ^ (2 : ℕ)
  let pR := 243 * a * e ^ (2 : ℕ) - 630 * b * c * e + 343 * c ^ (3 : ℕ)
  let d := m₀ * m₂ - m₁ ^ (2 : ℕ)
  let B := 9 * m₀ * e - 504 * m₁ * c + 15120 * m₂ * b - 181440 * m₃ * a
  let C := m₀ * m₃ ^ (2 : ℕ) - 2 * m₁ * m₂ * m₃ + m₂ ^ (3 : ℕ)
  have hd := det_primeArchSourceMomentHankelMatrix_two_pos
  rw [det_primeArchSourceMomentHankelMatrix_two] at hd
  change 0 < d at hd
  have hr := thetaCusp_radiusMixing_fifthMoment_gate
  change 0 ≤ 11 * qR * f - pR at hr
  have hmul := mul_nonneg hd.le hr
  have hdet :
      362880 * (primeArchSourceMomentHankelMatrix 3).det =
        d * (f - B) - 362880 * C := by
    rw [det_primeArchSourceMomentHankelMatrix_three,
      normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment]
    dsimp [d, B, C, f, e, c, b, a, m₀, m₁, m₂, m₃]
    ring
  calc
    d * pR - 11 * qR * (d * B + 362880 * C) ≤
        11 * qR * (d * (f - B) - 362880 * C) := by nlinarith [hmul]
    _ = 362880 * 11 * qR * (primeArchSourceMomentHankelMatrix 3).det := by
      rw [← hdet]
      ring

end
end RHTower
