import GaloisForLFunctions.RHTower.Suzuki.SuzukiSafeShiftResponseChargeCancellation
import GaloisForLFunctions.RHTower.TraceHankelConverse

/-!
# Degree-one atomwise no-go for shifted Xi trace forms

At a nonreal spectral atom, evaluation of real affine polynomials is surjective onto `ℂ`.  A
complex phase can therefore rotate `lambda p(lambda)^(2 : ℕ)` into the negative real half-line.  Applied
to every positive mass shift of the reciprocal-square Xi divisor, this proves:

* every off-critical zero has a degree-at-most-one polynomial with strictly negative atomwise
  trace contribution;
* atomwise nonnegativity for all affine real polynomials is equivalent to RH, at every positive
  shift.

Consequently any mass-shifted spectral-face proof must use cross-orbit cancellation.  An atomwise
positivity argument cannot be a weaker route to RH.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

theorem natDegree_realLinearInterpolator_le_one_xiShiftedAtomwisePositivityNoGo (alpha c : ℂ) :
    (realLinearInterpolator alpha c).natDegree <= 1 := by
  change (C (c.re - (c.im / alpha.im) * alpha.re) +
    C (c.im / alpha.im) * X).natDegree <= 1
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  apply max_le
  · rw [Polynomial.natDegree_C]
    omega
  · simpa only [pow_one] using
      (Polynomial.natDegree_C_mul_X_pow_le (c.im / alpha.im) 1)

/-- A nonreal atom admits a real affine test with strictly negative weighted square. -/
theorem exists_affine_traceAtom_re_neg {lambda : ℂ} (him : lambda.im ≠ 0) :
    ∃ p : Polynomial ℝ,
      p.natDegree <= 1 ∧
        (lambda * evalRealPolynomial p lambda ^ (2 : ℕ)).re < 0 := by
  obtain ⟨c, hc⟩ := exists_phase_sq_re_neg him
  refine ⟨realLinearInterpolator lambda c,
    natDegree_realLinearInterpolator_le_one_xiShiftedAtomwisePositivityNoGo lambda c, ?_⟩
  rw [evalRealLinearInterpolator him]
  exact hc

/-- Every off-critical Xi zero produces a degree-one negative atom after every positive mass
shift. -/
theorem exists_affine_xiShifted_traceAtom_re_neg
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ p : Polynomial ℝ,
      p.natDegree <= 1 ∧
        (xiShiftedReciprocalSquare y q *
          evalRealPolynomial p (xiShiftedReciprocalSquare y q) ^ (2 : ℕ)).re < 0 := by
  have him : (xiShiftedReciprocalSquare y q).im ≠ 0 := by
    exact (xiShiftedReciprocalSquare_im_eq_zero_iff_criticalLine hy q).not.mpr hoff
  exact exists_affine_traceAtom_re_neg him

/-- Atomwise affine positivity at one positive shift forces every Xi zero onto the critical
line. -/
theorem criticalLine_of_xiShifted_atomwiseAffine_nonneg
    {y : ℝ} (hy : 0 < y)
    (hpos : ∀ (q : XiZeroCopy) (p : Polynomial ℝ),
      p.natDegree <= 1 →
        0 <= (xiShiftedReciprocalSquare y q *
          evalRealPolynomial p (xiShiftedReciprocalSquare y q) ^ (2 : ℕ)).re) :
    ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
  intro q
  by_contra hoff
  obtain ⟨p, hpdeg, hpneg⟩ :=
    exists_affine_xiShifted_traceAtom_re_neg hy q hoff
  exact (not_lt_of_ge (hpos q p hpdeg)) hpneg

/-- **Atomwise degree-one no-go, exact form.**  At every positive mass shift, nonnegativity of
each individual shifted Xi atom against every real affine polynomial is equivalent to RH. -/
theorem xiShifted_atomwiseAffine_nonneg_iff_riemannHypothesis
    {y : ℝ} (hy : 0 < y) :
    (∀ (q : XiZeroCopy) (p : Polynomial ℝ),
      p.natDegree <= 1 →
        0 <= (xiShiftedReciprocalSquare y q *
          evalRealPolynomial p (xiShiftedReciprocalSquare y q) ^ (2 : ℕ)).re) ↔
      RiemannHypothesis := by
  constructor
  · intro hpos
    have hline := criticalLine_of_xiShifted_atomwiseAffine_nonneg hy hpos
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH q p _hpdeg
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have hline : (q.1 : ℂ).re = 1 / 2 := by
      have him := congrArg Complex.im ht
      simp [xiSpectralPoint] at him
      linarith
    have himlambda : (xiShiftedReciprocalSquare y q).im = 0 :=
      (xiShiftedReciprocalSquare_im_eq_zero_iff_criticalLine hy q).mpr hline
    have hlambda : xiShiftedReciprocalSquare y q =
        ((xiShiftedReciprocalSquare y q).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using himlambda
    rw [hlambda, evalRealPolynomial_ofReal]
    have hmass : 0 <= (xiShiftedReciprocalSquare y q).re := by
      simpa only [xiShiftedResponseMass] using
        (xiShiftedResponseMass_pos hy q).le
    simpa [Complex.mul_re, Complex.mul_im, pow_two] using
      mul_nonneg hmass (sq_nonneg (Polynomial.eval
        (xiShiftedReciprocalSquare y q).re p))

end

end RHTower
