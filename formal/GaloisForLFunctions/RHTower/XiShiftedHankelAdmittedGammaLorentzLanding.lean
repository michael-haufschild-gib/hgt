import GaloisForLFunctions.RHTower.RouteRTwoThreeGammaCapComparison
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryHilbertChargeFlow
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule
import GaloisForLFunctions.RHTower.SquaredXiCompleteMonotonicity

/-!
# Admitted Gamma--Lorentz landing on shifted Hankel null flags

The fixed `(2,3)` cooriented Gamma exterior and the shifted-Hankel mixed
feature are both reflection-odd.  On one strict-right upper representative
of an off-line Xi quartet, the centered Gamma rate is exactly the imaginary
phase of the shifted reciprocal-square atom times a strictly positive gauge.

This produces a canonical source-first bilinear landing before quartet
aggregation.  A strictly positive normalization identifies that landing
with the reflection-even Lorentz shear.  The complete four-image shear is
four times the admitted landing.

The same theorem is also a sharp no-go: Gamma orientation changes the gauge
but not the sign of the adaptive mixed feature.  No Riemann-hypothesis,
Hankel-positivity, or first-crossing premise occurs.
-/

open Complex Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive change of gauge from shifted reciprocal imaginary phase to the
centered horizontal Xi rate on a strict-right upper quartet representative. -/
def xiRightUpperGammaPhaseGauge
    (y : ℝ) (q : XiRightUpperZeroCopy) : ℝ :=
  Complex.normSq ((q.1.1.1 : ℂ) - 1 / 2) ^ (2 : ℕ) *
      Complex.normSq
        (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q.1.1) /
    (q.1.1.1 : ℂ).im

/-- Strict-right upper admission gives positive physical Xi height. -/
theorem xiRightUpper_support_im_pos (q : XiRightUpperZeroCopy) :
    0 < (q.1.1.1 : ℂ).im := by
  have h := q.2
  rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at h
  simpa using h

/-- Strict-right admission gives positive centered horizontal Xi rate. -/
theorem xiRightUpper_centeredRate_pos (q : XiRightUpperZeroCopy) :
    0 < primeDepthBVWoldXiCenteredRate q.1.1.1 := by
  have h := xiRightCenteredZero_re_pos q.1
  rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at h
  rw [primeDepthBVWoldXiCenteredRate]
  simp only [Complex.sub_re] at h
  norm_num at h ⊢
  linarith

/-- The Gamma/phase change of gauge is strictly positive at every positive
mass shift on the admitted right-upper domain. -/
theorem xiRightUpperGammaPhaseGauge_pos
    {y : ℝ} (hy : 0 < y) (q : XiRightUpperZeroCopy) :
    0 < xiRightUpperGammaPhaseGauge y q := by
  have hbase : 0 < Complex.normSq ((q.1.1.1 : ℂ) - 1 / 2) :=
    Complex.normSq_pos.mpr
      (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1.1.1))
  have hden : 0 < Complex.normSq
      (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q.1.1) :=
    Complex.normSq_pos.mpr
      (one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy.le q.1.1)
  exact div_pos (mul_pos (sq_pos_of_pos hbase) hden)
    (xiRightUpper_support_im_pos q)

/-- **Exact Gamma/phase coordinate identity.**  Centered Xi rate and shifted
reciprocal imaginary phase are one odd coordinate in two positive gauges. -/
theorem primeDepthBVWoldXiCenteredRate_eq_gammaPhaseGauge_mul_shiftedIm
    {y : ℝ} (hy : 0 < y) (q : XiRightUpperZeroCopy) :
    primeDepthBVWoldXiCenteredRate q.1.1.1 =
      xiRightUpperGammaPhaseGauge y q *
        (xiShiftedReciprocalSquare y q.1.1).im := by
  let D₀ : ℝ := Complex.normSq ((q.1.1.1 : ℂ) - 1 / 2) ^ (2 : ℕ)
  let D₁ : ℝ := Complex.normSq
    (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q.1.1)
  have hD₀ : D₀ ≠ 0 := by
    exact pow_ne_zero 2 (Complex.normSq_pos.mpr
      (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1.1.1))).ne'
  have hD₁ : D₁ ≠ 0 := by
    exact (Complex.normSq_pos.mpr
      (one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy.le q.1.1)).ne'
  have hheight : (q.1.1.1 : ℂ).im ≠ 0 :=
    (xiRightUpper_support_im_pos q).ne'
  have hcentral : (xiZeroCopyReciprocalSquare q.1.1).im =
      primeDepthBVWoldXiCenteredRate q.1.1.1 *
        (q.1.1.1 : ℂ).im / D₀ := by
    rw [xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare_im]
    dsimp only [D₀, primeDepthBVWoldXiCenteredRate]
    ring
  have hshift : (xiShiftedReciprocalSquare y q.1.1).im =
      primeDepthBVWoldXiCenteredRate q.1.1.1 *
        (q.1.1.1 : ℂ).im / (D₀ * D₁) := by
    rw [xiShiftedReciprocalSquare_im_formula, hcentral]
    change (_ / D₀) / D₁ = _
    field_simp [hD₀, hD₁]
  rw [xiRightUpperGammaPhaseGauge, hshift]
  change primeDepthBVWoldXiCenteredRate q.1.1.1 =
    (D₀ * D₁ / (q.1.1.1 : ℂ).im) *
      (primeDepthBVWoldXiCenteredRate q.1.1.1 *
        (q.1.1.1 : ℂ).im / (D₀ * D₁))
  field_simp [hD₀, hD₁, hheight]

/-- Actual cooriented Gamma exterior on the canonical `(2,3)` source face,
labelled by one admitted Xi quartet representative. -/
def xiRightUpperTwoThreeGammaExterior
    (q : XiRightUpperZeroCopy) : ℝ :=
  xiGammaEulerPrimitiveCoorientedReflectionOddExterior
    (primeDepthBVWoldXiCenteredRate q.1.1.1)
    (routeRTwoPrime, 0) (routeRThreePrime, 0)

/-- The admitted `(2,3)` Gamma exterior is centered rate times its positive
source gauge. -/
theorem xiRightUpperTwoThreeGammaExterior_eq_centeredRate_mul_gauge
    (q : XiRightUpperZeroCopy) :
    xiRightUpperTwoThreeGammaExterior q =
      primeDepthBVWoldXiCenteredRate q.1.1.1 *
        routeRTwoThreeGammaCoorientedGauge q.1.1.1 := by
  rw [xiRightUpperTwoThreeGammaExterior,
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge]
  rfl

/-- The actual admitted `(2,3)` Gamma exterior is strictly positive. -/
theorem xiRightUpperTwoThreeGammaExterior_pos
    (q : XiRightUpperZeroCopy) :
    0 < xiRightUpperTwoThreeGammaExterior q := by
  rw [xiRightUpperTwoThreeGammaExterior_eq_centeredRate_mul_gauge]
  exact mul_pos (xiRightUpper_centeredRate_pos q)
    (routeRTwoThreeGammaCoorientedGauge_pos q.1.1.1)

/-- Unnormalized source-first bilinear pairing of actual Gamma orientation
with the odd adaptive mixed feature. -/
def xiRightUpperGammaLorentzRawLanding
    (y : ℝ) (p : Polynomial ℝ) (q : XiRightUpperZeroCopy) : ℝ :=
  xiRightUpperTwoThreeGammaExterior q *
    xiShiftedApertureMixedPairTerm y p p q.1.1

/-- Positive admission normalization which converts the raw Gamma/mixed
pairing into the Lorentz shear gauge. -/
def xiRightUpperGammaLorentzNormalization
    (y : ℝ) (q : XiRightUpperZeroCopy) : ℝ :=
  2 * ‖xiShiftedReciprocalSquare y q.1.1‖ /
    ((xiShiftedReciprocalSquare y q.1.1).re *
      xiRightUpperGammaPhaseGauge y q *
        routeRTwoThreeGammaCoorientedGauge q.1.1.1)

/-- The Gamma-to-Lorentz normalization is strictly positive. -/
theorem xiRightUpperGammaLorentzNormalization_pos
    {y : ℝ} (hy : 0 < y) (q : XiRightUpperZeroCopy) :
    0 < xiRightUpperGammaLorentzNormalization y q := by
  have hnorm : 0 < ‖xiShiftedReciprocalSquare y q.1.1‖ :=
    norm_pos_iff.mpr (xiShiftedReciprocalSquare_ne_zero hy.le q.1.1)
  have hre : 0 < (xiShiftedReciprocalSquare y q.1.1).re := by
    simpa only [xiShiftedResponseMass] using
      xiShiftedResponseMass_pos hy q.1.1
  exact div_pos (mul_pos (by norm_num) hnorm)
    (mul_pos (mul_pos hre (xiRightUpperGammaPhaseGauge_pos hy q))
      (routeRTwoThreeGammaCoorientedGauge_pos q.1.1.1))

/-- Canonically normalized source-first bilinear landing, defined before
any reflection aggregation. -/
def xiRightUpperGammaLorentzLanding
    (y : ℝ) (p : Polynomial ℝ) (q : XiRightUpperZeroCopy) : ℝ :=
  xiRightUpperGammaLorentzNormalization y q *
    xiRightUpperGammaLorentzRawLanding y p q

/-- **Admitted Gamma--Lorentz landing theorem.**  The normalized bilinear
source landing is exactly the phase-weighted Lorentz shear atom. -/
theorem xiRightUpperGammaLorentzLanding_eq_shear
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ)
    (q : XiRightUpperZeroCopy) :
    xiRightUpperGammaLorentzLanding y p q =
      xiShiftedApertureLorentzShearTerm y p q.1.1 := by
  have hre : (xiShiftedReciprocalSquare y q.1.1).re ≠ 0 :=
    (by simpa only [xiShiftedResponseMass] using
      (xiShiftedResponseMass_pos hy q.1.1).ne')
  have hphase : xiRightUpperGammaPhaseGauge y q ≠ 0 :=
    (xiRightUpperGammaPhaseGauge_pos hy q).ne'
  have hgamma : routeRTwoThreeGammaCoorientedGauge q.1.1.1 ≠ 0 :=
    (routeRTwoThreeGammaCoorientedGauge_pos q.1.1.1).ne'
  rw [xiRightUpperGammaLorentzLanding,
    xiRightUpperGammaLorentzRawLanding,
    xiRightUpperGammaLorentzNormalization,
    xiRightUpperTwoThreeGammaExterior_eq_centeredRate_mul_gauge,
    primeDepthBVWoldXiCenteredRate_eq_gammaPhaseGauge_mul_shiftedIm hy,
    xiShiftedApertureLorentzShearTerm_eq_phaseWeight_mul_mixed hy]
  field_simp [hre, hphase, hgamma]

/-- Positive Gamma normalization cannot manufacture a sign: raw bilinear
landing is positive exactly when the target Lorentz shear is positive. -/
theorem xiRightUpperGammaLorentzRawLanding_pos_iff_shear_pos
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ)
    (q : XiRightUpperZeroCopy) :
    0 < xiRightUpperGammaLorentzRawLanding y p q ↔
      0 < xiShiftedApertureLorentzShearTerm y p q.1.1 := by
  rw [← xiRightUpperGammaLorentzLanding_eq_shear hy p q,
    xiRightUpperGammaLorentzLanding]
  constructor
  · exact mul_pos (xiRightUpperGammaLorentzNormalization_pos hy q)
  · intro h
    by_contra hraw
    have hnonpos : xiRightUpperGammaLorentzRawLanding y p q ≤ 0 :=
      le_of_not_gt hraw
    have := mul_nonpos_of_nonneg_of_nonpos
      (xiRightUpperGammaLorentzNormalization_pos hy q).le hnonpos
    linarith

/-- Positive Gamma normalization preserves the zero locus as well. -/
theorem xiRightUpperGammaLorentzRawLanding_eq_zero_iff_shear_eq_zero
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ)
    (q : XiRightUpperZeroCopy) :
    xiRightUpperGammaLorentzRawLanding y p q = 0 ↔
      xiShiftedApertureLorentzShearTerm y p q.1.1 = 0 := by
  rw [← xiRightUpperGammaLorentzLanding_eq_shear hy p q,
    xiRightUpperGammaLorentzLanding, mul_eq_zero]
  exact (or_iff_right
    (xiRightUpperGammaLorentzNormalization_pos hy q).ne').symm

/-- Functional-equation reflection fixes every shifted reciprocal-square
atom because it negates the centered spectral coordinate before squaring. -/
theorem xiShiftedReciprocalSquare_reflect
    (y : ℝ) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare y (xiZeroCopyReflectEquiv q) =
      xiShiftedReciprocalSquare y q := by
  simp [xiShiftedReciprocalSquare, xiZeroCopyReciprocalSquare,
    xiSpectralPoint_reflect]

/-- Functional-equation reflection fixes the marked Lorentz shear. -/
theorem xiShiftedApertureLorentzShearTerm_reflect
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureLorentzShearTerm y p (xiZeroCopyReflectEquiv q) =
      xiShiftedApertureLorentzShearTerm y p q := by
  simp [xiShiftedApertureLorentzShearTerm,
    xiShiftedApertureShearedEvaluation,
    xiShiftedReciprocalSquare_reflect]

/-- Schwarz conjugation fixes the sheared real evaluation. -/
theorem xiShiftedApertureShearedEvaluation_copyConj
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureShearedEvaluation y p (xiZeroCopyConjEquiv q) =
      xiShiftedApertureShearedEvaluation y p q := by
  rw [xiShiftedApertureShearedEvaluation,
    xiShiftedApertureShearedEvaluation,
    xiShiftedReciprocalSquare_copyConj hy,
    evalRealPolynomial_conj]
  simp
  ring

/-- Schwarz conjugation fixes the marked Lorentz shear. -/
theorem xiShiftedApertureLorentzShearTerm_copyConj
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureLorentzShearTerm y p (xiZeroCopyConjEquiv q) =
      xiShiftedApertureLorentzShearTerm y p q := by
  simp only [xiShiftedApertureLorentzShearTerm,
    xiShiftedReciprocalSquare_copyConj hy,
    xiShiftedApertureShearedEvaluation_copyConj hy,
    evalRealPolynomial_conj, Complex.conj_re, Complex.conj_im,
    Complex.normSq_conj]
  ring

/-- Every member of the FE--Schwarz quartet has the same even Lorentz shear. -/
theorem xiShiftedApertureLorentzShearTerm_quadPart
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ)
    (q : XiZeroCopy) (c r : Bool) :
    xiShiftedApertureLorentzShearTerm y p (xiWardQuadPart c r q) =
      xiShiftedApertureLorentzShearTerm y p q := by
  cases c <;> cases r
  · rfl
  · exact xiShiftedApertureLorentzShearTerm_reflect y p q
  · exact xiShiftedApertureLorentzShearTerm_copyConj hy p q
  · exact xiShiftedApertureLorentzShearTerm_lineConj y p q

/-- **Completed quartet recovery.**  Aggregating after the admitted
source-first landing gives exactly the full four-image Lorentz shear. -/
theorem sum_xiWardQuadrupleEmbed_lorentzShear_eq_four_mul_gammaLanding
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ)
    (q : XiRightUpperZeroCopy) :
    (∑ cr : Bool × Bool,
      xiShiftedApertureLorentzShearTerm y p
        (xiWardQuadrupleEmbed (cr, q))) =
      4 * xiRightUpperGammaLorentzLanding y p q := by
  calc
    (∑ cr : Bool × Bool,
        xiShiftedApertureLorentzShearTerm y p
          (xiWardQuadrupleEmbed (cr, q))) =
        ∑ _cr : Bool × Bool,
          xiShiftedApertureLorentzShearTerm y p q.1.1 := by
            apply Finset.sum_congr rfl
            intro cr _
            exact xiShiftedApertureLorentzShearTerm_quadPart
              hy.le p q.1.1 cr.1 cr.2
    _ = 4 * xiShiftedApertureLorentzShearTerm y p q.1.1 := by
      norm_num
    _ = 4 * xiRightUpperGammaLorentzLanding y p q := by
      rw [xiRightUpperGammaLorentzLanding_eq_shear hy]

/-- Coefficient-faithful admitted landing for the polynomial carried by one
adaptive shifted-Hankel coefficient vector.  The same `c` defines its
factorial-diagonal `P^sharp` source representation. -/
def xiRightUpperGammaAdaptiveCoefficientLanding
    (y : ℝ) {N : ℕ} (c : Fin N → ℝ)
    (q : XiRightUpperZeroCopy) : ℝ :=
  xiRightUpperGammaLorentzLanding y (Polynomial.ofFn N c) q

/-- The coefficient-faithful admitted landing is exactly the adaptive
Lorentz shear before reflection aggregation. -/
theorem xiRightUpperGammaAdaptiveCoefficientLanding_eq_shear
    {y : ℝ} (hy : 0 < y) {N : ℕ} (c : Fin N → ℝ)
    (q : XiRightUpperZeroCopy) :
    xiRightUpperGammaAdaptiveCoefficientLanding y c q =
      xiShiftedApertureLorentzShearTerm y (Polynomial.ofFn N c) q.1.1 :=
  xiRightUpperGammaLorentzLanding_eq_shear hy _ q

/-- Quartet aggregation retains the coefficient-faithful adaptive landing
selected before completion. -/
theorem sum_xiWardQuadrupleEmbed_adaptiveLorentzShear_eq_four_mul_gammaLanding
    {y : ℝ} (hy : 0 < y) {N : ℕ} (c : Fin N → ℝ)
    (q : XiRightUpperZeroCopy) :
    (∑ cr : Bool × Bool,
      xiShiftedApertureLorentzShearTerm y (Polynomial.ofFn N c)
        (xiWardQuadrupleEmbed (cr, q))) =
      4 * xiRightUpperGammaAdaptiveCoefficientLanding y c q :=
  sum_xiWardQuadrupleEmbed_lorentzShear_eq_four_mul_gammaLanding
    hy _ q

end

end RHTower
