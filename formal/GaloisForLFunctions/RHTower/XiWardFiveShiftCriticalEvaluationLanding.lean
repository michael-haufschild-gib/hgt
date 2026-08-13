import GaloisForLFunctions.RHTower.XiWardFiveShiftEulerGammaPrimeGap
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureKernel
import GaloisForLFunctions.RHTower.CCMRectangularDirichletLandau

/-!
# Five-shift Euler–Gamma separator on critical source evaluations

The one-sided five-shift feature retains its favorable Euler sign after landing on the
concrete critical rigging: it is exactly a weighted energy current of five translated
continuous evaluations.  The current annihilates every critical-line evaluation, is
strictly positive at every right displacement seen by a nonzero evaluation, and is
nonpositive at every literal von Mangoldt depth.

This is a source-side identity for each evaluation vector.  It does not assert the global
frame or trace estimate needed to sum these pointwise charges over the Xi divisor.
-/

open Complex

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Five translated critical-evaluation energies with the prime-gap coefficients. -/
def fiveShiftCriticalEvaluationEnergyCurrent
    (r : ℝ) (hr : 0 ≤ r) (z : ℂ) (hz : |z.im| < 1 / 2)
    (f : CriticalL2) : ℝ :=
  let q := Real.exp (-2 * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  (-(t * q * u) *
      (Real.exp r * Complex.normSq
        (criticalEvaluation z hz (criticalShift r hr f))) +
    (t * q + t * u + q * u + t * q * u) *
      (Real.exp (2 * r) * Complex.normSq
        (criticalEvaluation z hz
          (criticalShift (2 * r) (by nlinarith) f))) -
    (t + q + u + t * q + t * u + q * u) *
      (Real.exp (3 * r) * Complex.normSq
        (criticalEvaluation z hz
          (criticalShift (3 * r) (by nlinarith) f))) +
    (1 + t + q + u) *
      (Real.exp (4 * r) * Complex.normSq
        (criticalEvaluation z hz
          (criticalShift (4 * r) (by nlinarith) f))) -
    Real.exp (5 * r) * Complex.normSq
      (criticalEvaluation z hz
        (criticalShift (5 * r) (by nlinarith) f)))

/-- Exact source landing: the five-shift current factors into the prime-gap separator and
the unshifted evaluation energy. -/
theorem fiveShiftCriticalEvaluationEnergyCurrent_eq
    (r : ℝ) (hr : 0 ≤ r) (z : ℂ) (hz : |z.im| < 1 / 2)
    (f : CriticalL2) :
    fiveShiftCriticalEvaluationEnergyCurrent r hr z hz f =
      fiveShiftEulerGammaFeature r (-z.im) *
        Complex.normSq (criticalEvaluation z hz f) := by
  rw [fiveShiftCriticalEvaluationEnergyCurrent]
  rw [criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
  have henergy (L : ℝ) :
      Real.exp L *
          (Complex.normSq (normalizedRealSourceShiftMultiplier L z) *
            Complex.normSq (criticalEvaluation z hz f)) =
        centeredRealSourceShiftEnergyGain L z *
          Complex.normSq (criticalEvaluation z hz f) := by
    rw [centeredRealSourceShiftEnergyGain]
    ring
  rw [henergy r, henergy (2 * r), henergy (3 * r),
    henergy (4 * r), henergy (5 * r)]
  change
    -(Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) *
        Real.exp (-(21 / 10 : ℝ) * r)) *
          (centeredRealSourceShiftEnergyGain r z *
            Complex.normSq (criticalEvaluation z hz f)) +
      (Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-2 * r) * Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) *
            Real.exp (-(21 / 10 : ℝ) * r)) *
          (centeredRealSourceShiftEnergyGain (2 * r) z *
            Complex.normSq (criticalEvaluation z hz f)) -
      (Real.exp (-(6 / 5 : ℝ) * r) + Real.exp (-2 * r) +
          Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-2 * r) * Real.exp (-(21 / 10 : ℝ) * r)) *
          (centeredRealSourceShiftEnergyGain (3 * r) z *
            Complex.normSq (criticalEvaluation z hz f)) +
      (1 + Real.exp (-(6 / 5 : ℝ) * r) + Real.exp (-2 * r) +
          Real.exp (-(21 / 10 : ℝ) * r)) *
          (centeredRealSourceShiftEnergyGain (4 * r) z *
            Complex.normSq (criticalEvaluation z hz f)) -
      centeredRealSourceShiftEnergyGain (5 * r) z *
          Complex.normSq (criticalEvaluation z hz f) = _
  rw [fiveShiftEulerGammaFeature_eq_sourceEnergy]
  ring

/-- Diagonal multiplicity contributes exactly zero, for every source vector. -/
theorem fiveShiftCriticalEvaluationEnergyCurrent_diagonal
    (r : ℝ) (hr : 0 ≤ r) (z : ℂ) (hz : |z.im| < 1 / 2)
    (him : z.im = 0) (f : CriticalL2) :
    fiveShiftCriticalEvaluationEnergyCurrent r hr z hz f = 0 := by
  rw [fiveShiftCriticalEvaluationEnergyCurrent_eq, him, neg_zero,
    fiveShiftEulerGammaFeature_zero, zero_mul]

/-- A positive real displacement is separated strictly whenever the source evaluation sees it. -/
theorem fiveShiftCriticalEvaluationEnergyCurrent_pos
    {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (z : ℂ) (hz : |z.im| < 1 / 2) (him : -z.im = a)
    (f : CriticalL2) (heval : criticalEvaluation z hz f ≠ 0) :
    0 < fiveShiftCriticalEvaluationEnergyCurrent r hr.le z hz f := by
  rw [fiveShiftCriticalEvaluationEnergyCurrent_eq, him]
  exact mul_pos (fiveShiftEulerGammaFeature_pos hr ha0 ha)
    (Complex.normSq_pos.mpr heval)

/-- Every positive real displacement is seen strictly by every real-centered source feature. -/
theorem fiveShiftCriticalEvaluationEnergyCurrent_realFeature_pos
    {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) (him : -z.im = a) :
    0 < fiveShiftCriticalEvaluationEnergyCurrent r hr.le z hz
      (criticalFeature (t : ℂ) (by norm_num)) := by
  exact fiveShiftCriticalEvaluationEnergyCurrent_pos hr ha0 ha z hz him _
    (criticalEvaluation_realCriticalFeature_ne_zero t hz)

/-- Unconditional strict source charge for every actual multiplicity copy right of the line. -/
theorem fiveShiftCriticalEvaluationEnergyCurrent_xiRightZeroCopy_pos
    (r : ℝ) (hr : 0 < r) (t : ℝ) (q : XiRightZeroCopy) :
    0 < fiveShiftCriticalEvaluationEnergyCurrent r hr.le
      (xiSpectralPoint q.1) (abs_xiSpectralPoint_im_lt_half q.1)
      (criticalFeature (t : ℂ) (by norm_num)) := by
  apply fiveShiftCriticalEvaluationEnergyCurrent_realFeature_pos hr
    (xiRightCenteredZero_re_pos q)
    (le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2)
  rw [xiRightCenteredZero]
  simp [Complex.mul_re]

/-- Literal Euler frequencies have the opposite, nonpositive sign for every source vector. -/
theorem fiveShiftCriticalEvaluationEnergyCurrent_vonMangoldt_nonpos
    {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 2 ≤ n)
    (z : ℂ) (hz : |z.im| < 1 / 2) (him : -z.im = Real.log n)
    (f : CriticalL2) :
    fiveShiftCriticalEvaluationEnergyCurrent r hr z hz f ≤ 0 := by
  rw [fiveShiftCriticalEvaluationEnergyCurrent_eq, him]
  exact mul_nonpos_of_nonpos_of_nonneg
    (fiveShiftEulerGammaFeature_vonMangoldt_nonpos hr hn)
    (Complex.normSq_nonneg _)

end

end RHTower
