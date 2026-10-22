import GaloisForLFunctions.RHTower.XiWardCubicLogMomentEulerSource
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeTranslationAnomaly
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeCriticalRiggedCarrier

/-!
# Cubic separator from fixed source-translation energy

The cubic Hellinger feature is not inserted after divisor evaluation.  It is the difference of
the prime-normalized conormal energies of one fixed normalized real translation, observed at
scales `r / 2` and `r`.  At a centered Xi point with positive horizontal displacement `a`, this
difference is exactly

`exp (-a r) - exp (-2 a r)`.

It vanishes identically on the critical boundary, retains the cubic submicroscopic self-charge,
and is defined by fixed Hedenmalm source operations before divisor expansion.  This closes the
algebraic source-origin gate for the horizontal separator.  It does not assert the remaining
critical-rigging continuity or height-local arithmetic trace budget.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmPrimeTranslation

namespace HedenmalmThetaSource

/-- Normalized real translation extending `integerShift n` from `L = log n` to arbitrary scale. -/
def normalizedRealSourceShift (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-L / 2) : ℂ) * f (x + L)

/-- Conormal multiplier of the normalized real translation. -/
def normalizedRealSourceShiftMultiplier (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(L : ℂ) * dirichletExponent z)

/-- The fixed normalized real source translation has the literal continuous Dirichlet
character. -/
theorem sourceEvaluation_normalizedRealSourceShift
    (L : ℝ) (z : ℂ) (f : ℝ → ℂ) :
    sourceEvaluation z (normalizedRealSourceShift L f) =
      normalizedRealSourceShiftMultiplier L z * sourceEvaluation z f := by
  have htrans :
      ∫ x : ℝ, f (x + L) * HedenmalmQuantile.sourceChar z x =
        Complex.exp (-(Complex.I * z) * (L : ℂ)) *
          ∫ y : ℝ, f y * HedenmalmQuantile.sourceChar z y := by
    have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y => f y * HedenmalmQuantile.sourceChar z (y - L)) L
    simp only [add_sub_cancel_right] at h
    rw [h, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change f y * HedenmalmQuantile.sourceChar z (y - L) =
      Complex.exp (-(Complex.I * z) * (L : ℂ)) *
        (f y * HedenmalmQuantile.sourceChar z y)
    rw [HedenmalmPrimeTranslation.sourceChar_sub]
    ring
  change (∫ x : ℝ, (Real.exp (-L / 2) : ℂ) * f (x + L) *
      HedenmalmQuantile.sourceChar z x) =
    normalizedRealSourceShiftMultiplier L z *
      ∫ x : ℝ, f x * HedenmalmQuantile.sourceChar z x
  rw [show (fun x => (Real.exp (-L / 2) : ℂ) * f (x + L) *
        HedenmalmQuantile.sourceChar z x) =
      fun x => (Real.exp (-L / 2) : ℂ) *
        (f (x + L) * HedenmalmQuantile.sourceChar z x) by
      funext x
      ring]
  rw [MeasureTheory.integral_const_mul, htrans, ← mul_assoc]
  congr 1
  rw [normalizedRealSourceShiftMultiplier, dirichletExponent,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Arbitrary nonnegative real translation is bounded on the critical rigging and retains the
same exact conormal character as the algebraic source operation. -/
theorem criticalEvaluation_criticalShift
    (L : ℝ) (hL : 0 ≤ L) {z : ℂ} (hz : |z.im| < 1 / 2)
    (f : CriticalL2) :
    criticalEvaluation z hz (criticalShift L hL f) =
      normalizedRealSourceShiftMultiplier L z * criticalEvaluation z hz f := by
  rw [criticalEvaluation_eq_integral, criticalEvaluation_eq_integral]
  have hshift := criticalShift_ae L hL f
  rw [show (∫ x : ℝ, (criticalShift L hL f : ℝ → ℂ) x *
        HedenmalmQuantile.sourceChar z x) =
      sourceEvaluation z (normalizedRealSourceShift L f) by
    unfold sourceEvaluation
    apply integral_congr_ae
    filter_upwards [hshift] with x hx
    rw [hx]
    rfl]
  exact sourceEvaluation_normalizedRealSourceShift L z f

/-- Conormal evaluation is a literal continuous-dual eigenvector of every nonnegative real
critical shift.  This quotient-free identity is the operator-level input required by a trace. -/
theorem criticalEvaluation_comp_criticalShift
    (L : ℝ) (hL : 0 ≤ L) {z : ℂ} (hz : |z.im| < 1 / 2) :
    (criticalEvaluation z hz).comp (criticalShift L hL) =
      normalizedRealSourceShiftMultiplier L z • criticalEvaluation z hz := by
  ext f
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact criticalEvaluation_criticalShift L hL hz f

/-- Prime-normalized energy gain of a fixed real source translation. -/
def centeredRealSourceShiftEnergyGain (L : ℝ) (z : ℂ) : ℝ :=
  Real.exp L * Complex.normSq (normalizedRealSourceShiftMultiplier L z)

/-- The centered energy remembers only horizontal spectral displacement. -/
theorem centeredRealSourceShiftEnergyGain_eq_exp (L : ℝ) (z : ℂ) :
    centeredRealSourceShiftEnergyGain L z = Real.exp (2 * L * z.im) := by
  rw [centeredRealSourceShiftEnergyGain, normalizedRealSourceShiftMultiplier,
    Complex.normSq_eq_norm_sq, Complex.norm_exp]
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp [dirichletExponent, Complex.mul_re]
  ring

/-- Difference of the same fixed source-energy observable at scales `r / 2` and `r`. -/
def cubicTranslationEnergyFeature (r : ℝ) (z : ℂ) : ℝ :=
  centeredRealSourceShiftEnergyGain (r / 2) z -
    centeredRealSourceShiftEnergyGain r z

/-- Generic exponential form of the scale-difference feature. -/
theorem cubicTranslationEnergyFeature_eq_exp (r : ℝ) (z : ℂ) :
    cubicTranslationEnergyFeature r z =
      Real.exp (r * z.im) - Real.exp (2 * r * z.im) := by
  rw [cubicTranslationEnergyFeature,
    centeredRealSourceShiftEnergyGain_eq_exp,
    centeredRealSourceShiftEnergyGain_eq_exp]
  congr 1
  all_goals ring

/-- At a strict-right Xi copy the fixed source feature is exactly the Hellinger horizontal
feature, with no divisor-fitted normalization. -/
theorem cubicTranslationEnergyFeature_xiRightZeroCopy
    (r : ℝ) (q : XiRightZeroCopy) :
    cubicTranslationEnergyFeature r (xiSpectralPoint q.1) =
      Real.exp (-((xiRightCenteredZero q).re * r)) -
        Real.exp (-((2 * (xiRightCenteredZero q).re) * r)) := by
  rw [cubicTranslationEnergyFeature_eq_exp]
  simp only [xiRightCenteredZero, Complex.mul_re, I_re, I_im,
    zero_mul, one_mul, zero_sub]
  congr 1
  all_goals ring

/-- The feature is identically zero on the critical boundary. -/
theorem cubicTranslationEnergyFeature_eq_zero_of_spectral_im_eq_zero
    {z : ℂ} (hz : z.im = 0) (r : ℝ) :
    cubicTranslationEnergyFeature r z = 0 := by
  rw [cubicTranslationEnergyFeature_eq_exp, hz]
  norm_num

/-- Every positive scale detects every strict-right copy strictly positively, even arbitrarily
close to the critical boundary. -/
theorem cubicTranslationEnergyFeature_xiRightZeroCopy_pos
    {r : ℝ} (hr : 0 < r) (q : XiRightZeroCopy) :
    0 < cubicTranslationEnergyFeature r (xiSpectralPoint q.1) := by
  rw [cubicTranslationEnergyFeature_xiRightZeroCopy]
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  have ha := xiRightCenteredZero_re_pos q
  nlinarith

/-- On every source test, the difference of the two fixed normalized translation energies factors
as the Hellinger feature times unshifted conormal energy. -/
theorem sourceEvaluation_normalizedRealShiftEnergyDifference
    (r : ℝ) (z : ℂ) (f : ℝ → ℂ) :
    Real.exp (r / 2) * Complex.normSq
        (sourceEvaluation z (normalizedRealSourceShift (r / 2) f)) -
      Real.exp r * Complex.normSq
        (sourceEvaluation z (normalizedRealSourceShift r f)) =
      cubicTranslationEnergyFeature r z *
        Complex.normSq (sourceEvaluation z f) := by
  rw [sourceEvaluation_normalizedRealSourceShift,
    sourceEvaluation_normalizedRealSourceShift,
    Complex.normSq_mul, Complex.normSq_mul,
    ← mul_assoc, ← mul_assoc]
  change centeredRealSourceShiftEnergyGain (r / 2) z *
        Complex.normSq (sourceEvaluation z f) -
      centeredRealSourceShiftEnergyGain r z *
        Complex.normSq (sourceEvaluation z f) = _
  rw [cubicTranslationEnergyFeature]
  ring

/-- The two-scale separator is an exact energy difference of bounded operators on the critical
rigging, not only an identity on unbundled source functions. -/
theorem criticalEvaluation_criticalShiftEnergyDifference
    {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : |z.im| < 1 / 2)
    (f : CriticalL2) :
    Real.exp (r / 2) * Complex.normSq
        (criticalEvaluation z hz
          (criticalShift (r / 2) (div_nonneg hr (by norm_num)) f)) -
      Real.exp r * Complex.normSq
        (criticalEvaluation z hz (criticalShift r hr f)) =
      cubicTranslationEnergyFeature r z *
        Complex.normSq (criticalEvaluation z hz f) := by
  rw [criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    Complex.normSq_mul, Complex.normSq_mul,
    ← mul_assoc, ← mul_assoc]
  change centeredRealSourceShiftEnergyGain (r / 2) z *
        Complex.normSq (criticalEvaluation z hz f) -
      centeredRealSourceShiftEnergyGain r z *
        Complex.normSq (criticalEvaluation z hz f) = _
  rw [cubicTranslationEnergyFeature]
  ring

/-- The cubic Hellinger Gram is exactly the continuous Gram of fixed source-translation energy
differences on two strict-right Xi fibres. -/
theorem integral_cubicTranslationEnergyFeature_xiRightZeroCopy
    (q w : XiRightZeroCopy) :
    (∫ r : ℝ in Ioi 0, r ^ (2 : ℕ) *
      cubicTranslationEnergyFeature r (xiSpectralPoint q.1) *
      cubicTranslationEnergyFeature r (xiSpectralPoint w.1)) =
      cubicLogMomentHellingerHorizontalKernel
        (xiRightCenteredZero q).re (xiRightCenteredZero w).re := by
  rw [show (fun r : ℝ => r ^ (2 : ℕ) *
      cubicTranslationEnergyFeature r (xiSpectralPoint q.1) *
      cubicTranslationEnergyFeature r (xiSpectralPoint w.1)) =
      fun r : ℝ => r ^ (2 : ℕ) *
        (Real.exp (-((xiRightCenteredZero q).re * r)) -
          Real.exp (-((2 * (xiRightCenteredZero q).re) * r))) *
        (Real.exp (-((xiRightCenteredZero w).re * r)) -
          Real.exp (-((2 * (xiRightCenteredZero w).re) * r))) by
    funext r
    rw [cubicTranslationEnergyFeature_xiRightZeroCopy,
      cubicTranslationEnergyFeature_xiRightZeroCopy]]
  exact integral_cubicLogMomentHellingerHorizontalKernel
    (xiRightCenteredZero_re_pos q) (xiRightCenteredZero_re_pos w)

/-- Source-generated self-charge is uniformly at least `115/108` on every strict-right Xi copy
and diverges as the copy approaches the critical line. -/
theorem cubicTranslationEnergyFeature_xiRightZeroCopy_self_ge
    (q : XiRightZeroCopy) :
    115 / 108 ≤
      ∫ r : ℝ in Ioi 0, r ^ (2 : ℕ) *
        cubicTranslationEnergyFeature r (xiSpectralPoint q.1) *
        cubicTranslationEnergyFeature r (xiSpectralPoint q.1) := by
  rw [integral_cubicTranslationEnergyFeature_xiRightZeroCopy]
  apply cubicLogMomentHellingerHorizontalKernel_self_ge
    (xiRightCenteredZero_re_pos q)
  exact le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2

end HedenmalmThetaSource

end

end RHTower
