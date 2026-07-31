import GaloisForLFunctions.RHTower.PrimeArchThetaThermalSusceptibility
import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio

/-!
# Gaussian-aperture balance for the theta-cusp source

The first nonconstant prime--Gamma Hankel condition was previously approached through two
separate sufficient moment-ratio bounds.  This file records the exact unsplit condition.  If
`m_j = thetaCuspRawEvenMoment j` and `mu_j = m_(j+1) / m_j`, the source cubic factors as

`m_0 * m_1 * m_2 * (3 * mu_2 + 15 * mu_0 - 10 * mu_1)`.

Consequently the Hankel condition is equivalent, not merely implied, by the single three-state
mean balance

`10 * mu_1 <= 15 * mu_0 + 3 * mu_2`.

The same cubic is one composite of the adjacent weighted Turan defects

`D_1 = m_1^2 - (1/3) * m_0 * m_2`,
`D_2 = m_2^2 - (3/5) * m_1 * m_3`:

`cubic = 5 * (3 * m_2 * D_1 - m_0 * D_2)`.

These identities isolate the derivative that a source-specific Gaussian-aperture monotonicity
theorem would have to control.  The actual completed-source aperture moments and multiplicative
composite are defined below, and their zero-aperture balance is identified exactly with the
three-state condition.  No global monotonicity theorem is asserted here.

The final section proves an exact source-specific boundary fact used by the aperture analysis:
the first atom has positive logarithmic slope at the endpoint, with the derivative identity
formalized directly from the theta seed.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-! ### Exact first-atom endpoint slope -/

/-- Exact logarithmic slope of the first theta atom at the half-line endpoint. -/
def thetaCuspFirstAtomBoundaryLogSlope : ℝ :=
  9 / 2 - 2 * Real.pi + 6 / (2 * Real.pi - 3)

/-- The first theta atom is strictly positive at the half-line endpoint. -/
theorem thetaCuspSourceTerm_one_zero_pos :
    0 < thetaCuspSourceTerm 0 1 := by
  rw [thetaCuspSourceTerm, thetaCuspSeed]
  norm_num
  have : 0 < 2 * Real.pi - 3 := by nlinarith [Real.pi_gt_three]
  positivity

/-- The exact boundary logarithmic slope of the first theta atom is positive. -/
theorem thetaCuspFirstAtomBoundaryLogSlope_pos :
    0 < thetaCuspFirstAtomBoundaryLogSlope := by
  have hpLower : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpUpperDecimal : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hpUpper : Real.pi < (63 / 20 : ℝ) := by
    norm_num at hpUpperDecimal ⊢
    exact hpUpperDecimal
  have hden : 0 < 2 * (2 * Real.pi - 3) := by nlinarith
  have hfactor : 0 < 8 * (Real.pi + 63 / 20) - 30 := by nlinarith
  have hprod :
      0 < ((63 / 20 : ℝ) - Real.pi) *
        (8 * (Real.pi + 63 / 20) - 30) :=
    mul_pos (sub_pos.mpr hpUpper) hfactor
  have hnum : 0 < -8 * Real.pi ^ 2 + 30 * Real.pi - 15 := by
    nlinarith
  rw [thetaCuspFirstAtomBoundaryLogSlope]
  rw [show 9 / 2 - 2 * Real.pi + 6 / (2 * Real.pi - 3) =
      (-8 * Real.pi ^ 2 + 30 * Real.pi - 15) /
        (2 * (2 * Real.pi - 3)) by
    field_simp [ne_of_gt (by nlinarith : 0 < 2 * Real.pi - 3)]
    ring]
  exact div_pos hnum hden

/-- At the endpoint, the derivative of the first theta atom is its value times the exact
positive boundary logarithmic slope. -/
theorem hasDerivAt_thetaCuspSourceTerm_one_zero :
    HasDerivAt (fun x : ℝ => thetaCuspSourceTerm x 1)
      (thetaCuspFirstAtomBoundaryLogSlope * thetaCuspSourceTerm 0 1) 0 := by
  have ht : HasDerivAt (fun x : ℝ => Real.exp x) 1 0 := by
    simpa using Real.hasDerivAt_exp 0
  have hhalf : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (1 / 2) 0 := by
    convert (Real.hasDerivAt_exp (0 / 2)).comp 0
      ((hasDerivAt_id (x := (0 : ℝ))).div_const 2) using 1
    all_goals first | rfl | norm_num
  have ht2 := ht.pow 2
  have ht4 := ht.pow 4
  have hpoly := (ht4.const_mul (2 * Real.pi)).sub (ht2.const_mul 3)
  have hinner : HasDerivAt
      (fun x : ℝ => -Real.pi * Real.exp x ^ 2) (-2 * Real.pi) 0 := by
    convert ht2.const_mul (-Real.pi) using 1
    all_goals first | rfl | norm_num
    all_goals first | rfl | ring
  have hgauss : HasDerivAt
      (fun x : ℝ => Real.exp (-Real.pi * Real.exp x ^ 2))
        (Real.exp (-Real.pi) * (-2 * Real.pi)) 0 := by
    refine (HasDerivAt.comp_of_eq (x := (0 : ℝ)) (y := -Real.pi)
      (Real.hasDerivAt_exp (-Real.pi)) hinner (by norm_num)).congr_deriv ?_
    ring
  have hsource := ((hhalf.mul hpoly).mul hgauss).const_mul (2 * Real.pi)
  convert hsource using 1
  · exact rfl
  · exact rfl
  · funext x
    simp [thetaCuspSourceTerm, thetaCuspSeed]
    ring
  · simp [thetaCuspFirstAtomBoundaryLogSlope, thetaCuspSourceTerm, thetaCuspSeed]
    have hden : 2 * Real.pi - 3 ≠ 0 := by
      nlinarith [Real.pi_gt_three]
    field_simp [hden]
    ring

/-! ### The completed-source Gaussian aperture -/

/-- Even moment of the completed theta source after the Gaussian height contraction
`exp (lambda * x^2)`.  The research aperture uses `lambda ≤ 0`; at `lambda = 0` this is the
existing completed raw moment. -/
def thetaCuspGaussianApertureMoment (lambda : ℝ) (j : ℕ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) * thetaCuspFullSource x

/-- The single additive balance whose sign is the logarithmic derivative of the multiplicative
Gaussian-aperture composite. -/
def thetaCuspGaussianApertureBalance (lambda : ℝ) : ℝ :=
  3 * (thetaCuspGaussianApertureMoment lambda 3 /
      thetaCuspGaussianApertureMoment lambda 2) +
    15 * (thetaCuspGaussianApertureMoment lambda 1 /
      thetaCuspGaussianApertureMoment lambda 0) -
    10 * (thetaCuspGaussianApertureMoment lambda 2 /
      thetaCuspGaussianApertureMoment lambda 1)

/-- Multiplicative Gaussian-aperture observable selected by the exact source cubic. -/
def thetaCuspGaussianApertureComposite (lambda : ℝ) : ℝ :=
  thetaCuspGaussianApertureMoment lambda 0 ^ 15 *
      thetaCuspGaussianApertureMoment lambda 2 ^ 3 /
    thetaCuspGaussianApertureMoment lambda 1 ^ 10

/-- The completed Gaussian aperture specializes to the existing raw moment at zero tilt. -/
theorem thetaCuspGaussianApertureMoment_zero (j : ℕ) :
    thetaCuspGaussianApertureMoment 0 j = thetaCuspRawEvenMoment j := by
  simp [thetaCuspGaussianApertureMoment, thetaCuspRawEvenMoment]

/-- Exact zero-tilt value of the additive Gaussian-aperture balance. -/
theorem thetaCuspGaussianApertureBalance_zero :
    thetaCuspGaussianApertureBalance 0 =
      3 * (thetaCuspRawEvenMoment 3 / thetaCuspRawEvenMoment 2) +
        15 * (thetaCuspRawEvenMoment 1 / thetaCuspRawEvenMoment 0) -
        10 * (thetaCuspRawEvenMoment 2 / thetaCuspRawEvenMoment 1) := by
  simp only [thetaCuspGaussianApertureBalance,
    thetaCuspGaussianApertureMoment_zero]

/-- Raw sixth-seam numerator selected by the completed-source Gaussian-aperture asymptotic.
Writing `f_k = Phi^(k)(0)`, this is `f_0^2 f_6 - 15 f_0 f_2 f_4 + 30 f_2^3`.
It is recorded as an exact source object; no sign is assumed. -/
def thetaCuspGaussianApertureSixthSeamNumerator : ℝ :=
  thetaCuspFullSource 0 ^ 2 *
      iteratedDeriv 6 thetaCuspFullSource 0 -
    15 * thetaCuspFullSource 0 *
      iteratedDeriv 2 thetaCuspFullSource 0 *
      iteratedDeriv 4 thetaCuspFullSource 0 +
    30 * iteratedDeriv 2 thetaCuspFullSource 0 ^ 3

/-! ### One exact three-state balance -/

/-- The unsplit balance among the three consecutive size-biased theta means. -/
def ThetaCuspThreeTemperatureMeanBalance : Prop :=
  10 * thetaCuspSizeBiasedMean 1 ≤
    15 * thetaCuspSizeBiasedMean 0 +
      3 * thetaCuspSizeBiasedMean 2

/-- At zero Gaussian tilt, nonnegativity of the aperture balance is exactly the three-state
mean condition. -/
theorem thetaCuspGaussianApertureBalance_zero_nonneg_iff :
    0 ≤ thetaCuspGaussianApertureBalance 0 ↔
      ThetaCuspThreeTemperatureMeanBalance := by
  rw [thetaCuspGaussianApertureBalance_zero,
    ThetaCuspThreeTemperatureMeanBalance,
    thetaCuspSizeBiasedMean_eq_momentRatio,
    thetaCuspSizeBiasedMean_eq_momentRatio,
    thetaCuspSizeBiasedMean_eq_momentRatio]
  norm_num only [Nat.reduceAdd]
  constructor <;> intro h <;> linarith

/-- First weighted Turan defect of the completed theta moments. -/
def thetaCuspRawTuranDefectOne : ℝ :=
  thetaCuspRawEvenMoment 1 ^ 2 -
    (1 / 3 : ℝ) * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2

/-- Second weighted Turan defect of the completed theta moments. -/
def thetaCuspRawTuranDefectTwo : ℝ :=
  thetaCuspRawEvenMoment 2 ^ 2 -
    (3 / 5 : ℝ) * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3

/-- The exact source cubic is a single composite of two adjacent weighted Turan defects. -/
theorem thetaCusp_raw_cubic_eq_compositeTuran :
    3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 =
      5 * (3 * thetaCuspRawEvenMoment 2 * thetaCuspRawTuranDefectOne -
        thetaCuspRawEvenMoment 0 * thetaCuspRawTuranDefectTwo) := by
  rw [thetaCuspRawTuranDefectOne, thetaCuspRawTuranDefectTwo]
  ring

/-- Exact factorization of the source cubic by the positive lower moments and one unsplit
three-ratio balance. -/
theorem thetaCusp_raw_cubic_eq_threeTemperatureMeanBalance :
    3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 =
      thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
        thetaCuspRawEvenMoment 2 *
          (3 * (thetaCuspRawEvenMoment 3 / thetaCuspRawEvenMoment 2) +
            15 * (thetaCuspRawEvenMoment 1 / thetaCuspRawEvenMoment 0) -
            10 * (thetaCuspRawEvenMoment 2 / thetaCuspRawEvenMoment 1)) := by
  have h0 := (thetaCuspRawEvenMoment_pos 0).ne'
  have h1 := (thetaCuspRawEvenMoment_pos 1).ne'
  have h2 := (thetaCuspRawEvenMoment_pos 2).ne'
  field_simp [h0, h1, h2]

/-- The direct three-state mean balance is exactly nonnegativity of the raw source cubic. -/
theorem thetaCuspThreeTemperatureMeanBalance_iff_raw_cubic_nonneg :
    ThetaCuspThreeTemperatureMeanBalance ↔
      0 ≤ 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 := by
  rw [ThetaCuspThreeTemperatureMeanBalance,
    thetaCuspSizeBiasedMean_eq_momentRatio,
    thetaCuspSizeBiasedMean_eq_momentRatio,
    thetaCuspSizeBiasedMean_eq_momentRatio]
  norm_num only [Nat.reduceAdd]
  have hprod : 0 < thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
      thetaCuspRawEvenMoment 2 :=
    mul_pos (mul_pos (thetaCuspRawEvenMoment_pos 0)
      (thetaCuspRawEvenMoment_pos 1)) (thetaCuspRawEvenMoment_pos 2)
  have hbracket :
      (10 * (thetaCuspRawEvenMoment 2 / thetaCuspRawEvenMoment 1) ≤
        15 * (thetaCuspRawEvenMoment 1 / thetaCuspRawEvenMoment 0) +
          3 * (thetaCuspRawEvenMoment 3 / thetaCuspRawEvenMoment 2)) ↔
        0 ≤ 3 * (thetaCuspRawEvenMoment 3 / thetaCuspRawEvenMoment 2) +
          15 * (thetaCuspRawEvenMoment 1 / thetaCuspRawEvenMoment 0) -
          10 * (thetaCuspRawEvenMoment 2 / thetaCuspRawEvenMoment 1) := by
    constructor <;> intro h <;> linarith
  rw [hbracket, thetaCusp_raw_cubic_eq_threeTemperatureMeanBalance,
    mul_nonneg_iff_of_pos_left hprod]

/-- The normalized Hankel cubic is the raw cubic divided by the positive cube of the total
source mass. -/
theorem thetaCusp_normalized_cubic_eq_raw_div :
    3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
        15 * thetaCuspNormalizedEvenMoment 1 ^ 2 *
          thetaCuspNormalizedEvenMoment 2 -
        10 * thetaCuspNormalizedEvenMoment 2 ^ 2 =
      (3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2) /
          thetaCuspRawEvenMoment 0 ^ 3 := by
  simp only [thetaCuspNormalizedEvenMoment]
  field_simp [(thetaCuspRawEvenMoment_pos 0).ne']

/-- Nonnegativity of the raw cubic is exactly the existing normalized sixth-moment Hankel
condition. -/
theorem thetaCusp_raw_cubic_nonneg_iff_sixthMomentHankelInequality :
    (0 ≤ 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2) ↔
      ThetaCuspSixthMomentHankelInequality := by
  rw [ThetaCuspSixthMomentHankelInequality, thetaCusp_normalized_cubic_eq_raw_div]
  constructor
  · intro h
    exact div_nonneg h (pow_nonneg (thetaCuspRawEvenMoment_pos 0).le 3)
  · intro h
    have hden : 0 < thetaCuspRawEvenMoment 0 ^ 3 :=
      pow_pos (thetaCuspRawEvenMoment_pos 0) 3
    have hprod := mul_nonneg h hden.le
    rwa [div_mul_cancel₀ _ hden.ne'] at hprod

/-- **Exact replacement of the two sufficient ratio gates.**  The first nonconstant source
Hankel condition is equivalent to one three-state size-biased mean balance. -/
theorem thetaCuspThreeTemperatureMeanBalance_iff_sixthMomentHankelInequality :
    ThetaCuspThreeTemperatureMeanBalance ↔
      ThetaCuspSixthMomentHankelInequality :=
  thetaCuspThreeTemperatureMeanBalance_iff_raw_cubic_nonneg.trans
    thetaCusp_raw_cubic_nonneg_iff_sixthMomentHankelInequality

/-- Every real linear-polynomial prime--Gamma source Hankel test is nonnegative exactly when the
single three-state theta mean balance holds. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_iff_threeTemperatureMeanBalance :
    (∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re) ↔
      ThetaCuspThreeTemperatureMeanBalance := by
  constructor
  · intro h
    exact thetaCuspThreeTemperatureMeanBalance_iff_sixthMomentHankelInequality.mpr
      (forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality.mp h)
  · intro h
    exact forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality.mpr
      (thetaCuspThreeTemperatureMeanBalance_iff_sixthMomentHankelInequality.mp h)

end

end RHTower
