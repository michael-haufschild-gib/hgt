import GaloisForLFunctions.RHTower.PrimeArchThetaMonotoneGramRatio
import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence
import GaloisForLFunctions.RHTower.PrimeArchThetaShiftedGramGate

/-!
# A stronger four-moment constraint from monotonicity and the score recurrence

The decreasing theta density yields a multiplicative lower bound for the
shifted Gram residual.  The score recurrence upper-bounds the fifth moment.
Eliminating that moment tightens the four-moment Schur constraint.
-/

namespace RHTower
noncomputable section

/-- The Gram residual exceeds a fixed fraction of its four-moment boundary. -/
theorem thetaCuspNormalizedEvenMoment_shiftedGram_boundaryFraction :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let f := thetaCuspNormalizedEvenMoment 5
    let q := a * c - b ^ (2 : ℕ)
    let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
    (64 / 3905 : ℝ) * p ≤ q * f - p := by
  dsimp only
  let a := thetaCuspNormalizedEvenMoment 1
  let b := thetaCuspNormalizedEvenMoment 2
  let c := thetaCuspNormalizedEvenMoment 3
  let e := thetaCuspNormalizedEvenMoment 4
  let f := thetaCuspNormalizedEvenMoment 5
  let q := a * c - b ^ (2 : ℕ)
  let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
  have hr := thetaCuspNormalizedEvenMoment_shiftedGram_relative_floor
  change (64 / 3969 : ℝ) * q * f ≤ q * f - p at hr
  change (64 / 3905 : ℝ) * p ≤ q * f - p
  nlinarith [hr]

/-- Strictly sharper than the generic score–Schur constraint
`303*p < 145*q*e`: the monotone source contributes the factor `3905/3969`. -/
theorem thetaCusp_fourMoment_monotoneScoreSchurConstraint :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let q := a * c - b ^ (2 : ℕ)
    let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
    303 * 3969 * p ≤ 145 * 3905 * q * e := by
  dsimp only
  let a := thetaCuspNormalizedEvenMoment 1
  let b := thetaCuspNormalizedEvenMoment 2
  let c := thetaCuspNormalizedEvenMoment 3
  let e := thetaCuspNormalizedEvenMoment 4
  let f := thetaCuspNormalizedEvenMoment 5
  let q := a * c - b ^ (2 : ℕ)
  let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
  have hq := thetaCuspNormalizedEvenMoment_shifted_q_pos
  change 0 < q at hq
  have hr := thetaCuspNormalizedEvenMoment_shiftedGram_relative_floor
  change (64 / 3969 : ℝ) * q * f ≤ q * f - p at hr
  have hs := thetaCuspNormalizedEvenMoment_succ_le_score 4
  norm_num at hs
  change (303 : ℝ) * f ≤ 145 * e at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hq.le
  change (303 : ℝ) * 3969 * p ≤ 145 * 3905 * q * e
  nlinarith [hr, hscaled]

/-- The first open prime--archimedean determinant is bounded below by a
four-moment gate strengthened by the monotone theta residual. -/
theorem primeArch_three_det_monotoneGate_lower :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let m₀ := normalizedPrimeArchMoment 0
    let m₁ := normalizedPrimeArchMoment 1
    let m₂ := normalizedPrimeArchMoment 2
    let m₃ := normalizedPrimeArchMoment 3
    let q := a * c - b ^ (2 : ℕ)
    let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
    let d := m₀ * m₂ - m₁ ^ (2 : ℕ)
    let B := 9 * m₀ * e - 504 * m₁ * c + 15120 * m₂ * b - 181440 * m₃ * a
    let C := m₀ * m₃ ^ (2 : ℕ) - 2 * m₁ * m₂ * m₃ + m₂ ^ (3 : ℕ)
    (d * p - q * (d * B + 362880 * C)) + (64 / 3905 : ℝ) * d * p ≤
      362880 * q * (primeArchSourceMomentHankelMatrix 3).det := by
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
  let q := a * c - b ^ (2 : ℕ)
  let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
  let d := m₀ * m₂ - m₁ ^ (2 : ℕ)
  let B := 9 * m₀ * e - 504 * m₁ * c + 15120 * m₂ * b - 181440 * m₃ * a
  let C := m₀ * m₃ ^ (2 : ℕ) - 2 * m₁ * m₂ * m₃ + m₂ ^ (3 : ℕ)
  have hd := det_primeArchSourceMomentHankelMatrix_two_pos
  rw [det_primeArchSourceMomentHankelMatrix_two] at hd
  change 0 < d at hd
  have hres := thetaCuspNormalizedEvenMoment_shiftedGram_boundaryFraction
  change (64 / 3905 : ℝ) * p ≤ q * f - p at hres
  have hprod := mul_le_mul_of_nonneg_left hres hd.le
  have hEq := primeArch_three_det_shifted_theta_decomposition
  change 362880 * q * (primeArchSourceMomentHankelMatrix 3).det =
    d * (q * f - p) + (d * p - q * (d * B + 362880 * C)) at hEq
  rw [hEq]
  nlinarith [hprod]

end
end RHTower
