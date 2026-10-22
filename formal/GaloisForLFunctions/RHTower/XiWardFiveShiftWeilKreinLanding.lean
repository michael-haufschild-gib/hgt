import GaloisForLFunctions.RHTower.XiWardFiveShiftPairedSubmicroscopicSeparator
import GaloisForLFunctions.RHTower.GaussHodgeWeilKreinDecomposition
import GaloisForLFunctions.RHTower.CCM.CCMRectangularDirichletLandau

/-!
# Five-shift Euler–Gamma separator in the Xi Weil–Krein trace

The functional-equation-paired five-shift feature is not an abstract receiver: it is exactly
a weighted combination of reflection-difference energies of five exponential Weil tests on
every actual multiplicity copy of the Xi divisor.  Thus the raw feature lands unconditionally
in the negative Krein sector of the multiplicity-exact Weil trace.

Quadratic coalescence at the critical line forces inverse-square transverse Green
normalization.  After this normalization, every actual right-half divisor copy carries at
least `1/81` at scale one.  This module proves the exact zero-side landing.  It does not assert
the remaining source-side inverse-Green explicit formula or its arithmetic upper budget.
-/

open Complex

namespace RHTower

noncomputable section

def fiveShiftEulerGammaKreinDefectCombination (r : ℝ) (q0 : XiZeroCopy) : ℝ :=
  let q := Real.exp (-2 * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  t * q * u * ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp r)) q0‖ ^ 2 -
    (t * q + t * u + q * u + t * q * u) *
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (2 * r))) q0‖ ^ 2 +
    (t + q + u + t * q + t * u + q * u) *
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (3 * r))) q0‖ ^ 2 -
    (1 + t + q + u) *
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (4 * r))) q0‖ ^ 2 +
    ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (5 * r))) q0‖ ^ 2

theorem norm_sq_xiWeilPairDif_primeTest_exp
    {r : ℝ} (hr : 0 < r) (k : ℕ) (hk : 1 ≤ k) (q0 : XiZeroCopy) :
    ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (k * r))) q0‖ ^ 2 =
      Real.exp (2 * k * r * ((q0.1 : ℂ).re - 1 / 2)) +
        Real.exp (-2 * k * r * ((q0.1 : ℂ).re - 1 / 2)) - 2 := by
  have hkr : 0 < (k : ℝ) * r := mul_pos (by exact_mod_cast hk) hr
  have hp : 1 < Real.exp (k * r) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by exact_mod_cast hkr)
  rw [xiWeilPairDif, norm_sq_primeTest_sub_lineConj hp]
  have hpos := Real.exp_pos ((k : ℝ) * r)
  rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hpos]
  rw [Real.log_exp]
  ring

theorem fiveShiftEulerGammaKreinDefectCombination_eq_pairedFeature
    {r : ℝ} (hr : 0 < r) (q0 : XiZeroCopy) :
    fiveShiftEulerGammaKreinDefectCombination r q0 =
      fiveShiftEulerGammaPairedFeature r ((q0.1 : ℂ).re - 1 / 2) := by
  rw [fiveShiftEulerGammaKreinDefectCombination]
  let A : ℝ := (q0.1 : ℂ).re - 1 / 2
  let x : ℝ := Real.exp (-2 * r * A)
  have h1 := norm_sq_xiWeilPairDif_primeTest_exp hr 1 (by norm_num) q0
  have h2 := norm_sq_xiWeilPairDif_primeTest_exp hr 2 (by norm_num) q0
  have h3 := norm_sq_xiWeilPairDif_primeTest_exp hr 3 (by norm_num) q0
  have h4 := norm_sq_xiWeilPairDif_primeTest_exp hr 4 (by norm_num) q0
  have h5 := norm_sq_xiWeilPairDif_primeTest_exp hr 5 (by norm_num) q0
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul] at h1 h2 h3 h4 h5
  have hneg (k : ℕ) : Real.exp (-2 * k * r * A) = x ^ k := by
    change Real.exp (-2 * k * r * A) = Real.exp (-2 * r * A) ^ k
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpos (k : ℕ) : Real.exp (2 * k * r * A) = x⁻¹ ^ k := by
    change Real.exp (2 * k * r * A) = (Real.exp (-2 * r * A))⁻¹ ^ k
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have h1' :
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp r)) q0‖ ^ 2 =
        x + x⁻¹ - 2 := by
    rw [h1]
    change Real.exp (2 * r * A) + Real.exp (-2 * r * A) - 2 = _
    rw [show Real.exp (2 * r * A) = x⁻¹ ^ 1 by simpa using hpos 1,
      show Real.exp (-2 * r * A) = x ^ 1 by simpa using hneg 1]
    ring
  have h2' :
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (2 * r))) q0‖ ^ 2 =
        x ^ 2 + x⁻¹ ^ 2 - 2 := by
    rw [h2]
    rw [show Real.exp (4 * r * ((q0.1 : ℂ).re - 1 / 2)) = x⁻¹ ^ 2 by
        rw [← hpos 2]; dsimp [A]; congr 1; ring,
      show Real.exp (-4 * r * ((q0.1 : ℂ).re - 1 / 2)) = x ^ 2 by
        rw [← hneg 2]; dsimp [A]; congr 1; ring]
    ring
  have h3' :
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (3 * r))) q0‖ ^ 2 =
        x ^ 3 + x⁻¹ ^ 3 - 2 := by
    rw [h3]
    rw [show Real.exp (6 * r * ((q0.1 : ℂ).re - 1 / 2)) = x⁻¹ ^ 3 by
        rw [← hpos 3]; dsimp [A]; congr 1; ring,
      show Real.exp (-6 * r * ((q0.1 : ℂ).re - 1 / 2)) = x ^ 3 by
        rw [← hneg 3]; dsimp [A]; congr 1; ring]
    ring
  have h4' :
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (4 * r))) q0‖ ^ 2 =
        x ^ 4 + x⁻¹ ^ 4 - 2 := by
    rw [h4]
    rw [show Real.exp (8 * r * ((q0.1 : ℂ).re - 1 / 2)) = x⁻¹ ^ 4 by
        rw [← hpos 4]; dsimp [A]; congr 1; ring,
      show Real.exp (-8 * r * ((q0.1 : ℂ).re - 1 / 2)) = x ^ 4 by
        rw [← hneg 4]; dsimp [A]; congr 1; ring]
    ring
  have h5' :
      ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp (5 * r))) q0‖ ^ 2 =
        x ^ 5 + x⁻¹ ^ 5 - 2 := by
    rw [h5]
    rw [show Real.exp (10 * r * ((q0.1 : ℂ).re - 1 / 2)) = x⁻¹ ^ 5 by
        rw [← hpos 5]; dsimp [A]; congr 1; ring,
      show Real.exp (-10 * r * ((q0.1 : ℂ).re - 1 / 2)) = x ^ 5 by
        rw [← hneg 5]; dsimp [A]; congr 1; ring]
    ring
  rw [h1', h2', h3', h4', h5']
  rw [fiveShiftEulerGammaPairedFeature, fiveShiftEulerGammaFeature,
    fiveShiftEulerGammaFeature]
  have hfeaturePos :
      Real.exp (-2 * ((q0.1 : ℂ).re - 1 / 2) * r) = x := by
    dsimp [x, A]
    congr 1
    ring
  have hfeatureNeg :
      Real.exp (-2 * -((q0.1 : ℂ).re - 1 / 2) * r) = x⁻¹ := by
    rw [show -2 * -((q0.1 : ℂ).re - 1 / 2) * r =
        -(-2 * ((q0.1 : ℂ).re - 1 / 2) * r) by ring,
      Real.exp_neg, hfeaturePos]
  rw [hfeaturePos, hfeatureNeg]
  rw [fiveShiftEulerGammaPolynomial_eq_coefficients,
    fiveShiftEulerGammaPolynomial_eq_coefficients]
  ring

/-- The inverse-square transverse Green normalization of the five-shift negative Krein
sector.  The exponent two is forced by quadratic coalescence of a reflection pair at the
critical line. -/
def fiveShiftEulerGammaRenormalizedKreinDefectCombination
    (r : ℝ) (q0 : XiZeroCopy) : ℝ :=
  (((q0.1 : ℂ).re - 1 / 2)⁻¹) ^ 2 *
    fiveShiftEulerGammaKreinDefectCombination r q0

theorem fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_pairedFeature
    {r : ℝ} (hr : 0 < r) (q0 : XiZeroCopy) :
    fiveShiftEulerGammaRenormalizedKreinDefectCombination r q0 =
      fiveShiftEulerGammaPairedRenormalizedFeature r
        ((q0.1 : ℂ).re - 1 / 2) := by
  rw [fiveShiftEulerGammaRenormalizedKreinDefectCombination,
    fiveShiftEulerGammaKreinDefectCombination_eq_pairedFeature hr]
  rfl

/-- Every actual multiplicity copy strictly right of the critical line carries at least
`1/81` of inverse-square-renormalized five-shift negative Krein energy at source scale one. -/
theorem fiveShiftEulerGammaRenormalizedKreinDefectCombination_right_ge
    (q : XiRightZeroCopy) :
    1 / 81 ≤ fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q.1 := by
  rw [fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_pairedFeature
    (by norm_num)]
  have hcenter :
      ((q.1.1 : ℂ).re - 1 / 2) = (xiRightCenteredZero q).re := by
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint, Complex.sub_re]
    norm_num
  apply fiveShiftEulerGammaPairedRenormalizedFeature_one_ge
  · rw [hcenter]
    exact xiRightCenteredZero_re_pos q
  · rw [hcenter]
    exact le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2

end

end RHTower


