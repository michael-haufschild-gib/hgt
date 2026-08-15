import GaloisForLFunctions.RHTower.CompletedPrimeGammaMomentFarRightAsymptotic
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation
import GaloisForLFunctions.RHTower.CompletedPrimeGammaResolvedMomentColligation

/-!
# Strict center sign for the second completed odd moment

The reciprocal-square Xi divisor lies in the strict positive-real sector already established by
the endpoint theory.  Its cubic real part is therefore strictly positive term by term.  Summing
the multiplicity copies proves strict positivity of the second normalized prime--Gamma moment,
and hence of the corresponding completed odd logarithmic-derivative moment at the functional-
equation center.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every reciprocal-square Xi divisor atom has strictly positive cubic real part. -/
theorem xiZeroCopyReciprocalSquare_cube_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 3).re := by
  let z := xiZeroCopyReciprocalSquare q
  have hre : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hsector : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hformula :
      (z ^ 3).re = z.re * (z.re ^ 2 - 3 * z.im ^ 2) := by
    simp [pow_succ, Complex.mul_re]
    ring
  rw [hformula]
  exact mul_pos hre (by nlinarith [sq_pos_of_pos hre])

/-- The second normalized prime--Gamma moment is strictly positive unconditionally. -/
theorem normalizedPrimeArchMoment_two_pos :
    0 < normalizedPrimeArchMoment 2 := by
  have hpow :=
    summable_xiZeroCopyReciprocalSquare_pow 2
  have hre :
      Summable (fun q : XiZeroCopy =>
        (xiZeroCopyReciprocalSquare q ^ 3).re) :=
    Complex.reCLM.summable hpow
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow 2, Complex.re_tsum hpow]
  let q : XiZeroCopy := xiThermalEnumeration 0
  exact hre.tsum_pos
    (fun r => (xiZeroCopyReciprocalSquare_cube_re_pos r).le)
    q
    (xiZeroCopyReciprocalSquare_cube_re_pos q)

/-- Every linear source test whose two coefficients have the same weak sign is nonnegative.
This is unconditional: only the opposite-sign sector can contain the unresolved first Hankel
minor. -/
theorem primeArchSourceTraceHankel_linear_nonneg_of_coeff_mul_nonneg
    (a b : ℝ) (hsign : 0 ≤ a * b) :
    0 ≤ (primeArchSourceTraceHankel
      (Polynomial.C a + Polynomial.C b * Polynomial.X)).re := by
  rw [primeArchSourceTraceHankel_linear]
  have h0 : 0 ≤ normalizedPrimeArchMoment 0 :=
    normalizedPrimeArchMoment_zero_pos.le
  have h1 : 0 ≤ normalizedPrimeArchMoment 1 :=
    normalizedPrimeArchMoment_one_pos.le
  have h2 : 0 ≤ normalizedPrimeArchMoment 2 :=
    normalizedPrimeArchMoment_two_pos.le
  have hleft : 0 ≤ a ^ 2 * normalizedPrimeArchMoment 0 :=
    mul_nonneg (sq_nonneg a) h0
  have hmiddle : 0 ≤ 2 * a * b * normalizedPrimeArchMoment 1 := by
    exact mul_nonneg (by nlinarith) h1
  have hright : 0 ≤ b ^ 2 * normalizedPrimeArchMoment 2 :=
    mul_nonneg (sq_nonneg b) h2
  linarith

/-- The same-sign linear source cone is strictly positive away from the zero polynomial. -/
theorem primeArchSourceTraceHankel_linear_pos_of_coeff_mul_nonneg
    (a b : ℝ) (hsign : 0 ≤ a * b) (hne : a ≠ 0 ∨ b ≠ 0) :
    0 < (primeArchSourceTraceHankel
      (Polynomial.C a + Polynomial.C b * Polynomial.X)).re := by
  rw [primeArchSourceTraceHankel_linear]
  have hcross : 0 ≤ 2 * a * b * normalizedPrimeArchMoment 1 :=
    mul_nonneg (by nlinarith) normalizedPrimeArchMoment_one_pos.le
  rcases hne with ha | hb
  · have hlead : 0 < a ^ 2 * normalizedPrimeArchMoment 0 :=
      mul_pos (sq_pos_of_ne_zero ha) normalizedPrimeArchMoment_zero_pos
    have htail : 0 ≤ b ^ 2 * normalizedPrimeArchMoment 2 :=
      mul_nonneg (sq_nonneg b) normalizedPrimeArchMoment_two_pos.le
    linarith
  · have hlead : 0 ≤ a ^ 2 * normalizedPrimeArchMoment 0 :=
      mul_nonneg (sq_nonneg a) normalizedPrimeArchMoment_zero_pos.le
    have htail : 0 < b ^ 2 * normalizedPrimeArchMoment 2 :=
      mul_pos (sq_pos_of_ne_zero hb) normalizedPrimeArchMoment_two_pos
    linarith

/-- The paper's second completed odd logarithmic-derivative moment has positive center value. -/
theorem completedOddLogDerivMoment_two_one_half_re_pos :
    0 < (completedOddLogDerivMoment (1 / 2) 2).re := by
  rw [← completedMovingComplexMoment_eq_completedOddLogDerivMoment_one_half,
    completedMovingComplexMoment_one_half]
  exact normalizedPrimeArchMoment_two_pos

/-- The moving polynomial test for `P = X` is exactly the second completed odd moment. -/
theorem completedOddLogDerivPolynomialHankelReal_X
    (x : ℝ) :
    completedOddLogDerivPolynomialHankelReal
        (Polynomial.X : Polynomial ℝ) x =
      (completedOddLogDerivMoment (x : ℂ) 2).re := by
  rw [completedOddLogDerivPolynomialHankelReal_eq_sum]
  simp

/-- The `P = X` moving polynomial test is strictly positive at the center. -/
theorem completedOddLogDerivPolynomialHankelReal_X_one_half_pos :
    0 < completedOddLogDerivPolynomialHankelReal
      (Polynomial.X : Polynomial ℝ) (1 / 2) := by
  rw [completedOddLogDerivPolynomialHankelReal_X]
  simpa using completedOddLogDerivMoment_two_one_half_re_pos

/-- At the paper's far-right test point, the second completed moment equals its resolved source. -/
theorem completedOddLogDerivMoment_two_ten_re_eq_resolved :
    (completedOddLogDerivMoment (10 : ℂ) 2).re =
      completedPrimeGammaResolvedMoment 10 2 := by
  simpa using congrArg Complex.re
    (completedOddLogDerivMoment_ofReal_eq_resolved
      (x := (10 : ℝ)) (by norm_num) 2)

/-- The far-right test moment is exactly its Euler, Gamma, and polar decomposition. -/
theorem completedOddLogDerivMoment_two_ten_re_eq_source :
    (completedOddLogDerivMoment (10 : ℂ) 2).re =
      infiniteVonMangoldtGammaRawMoment 9 5 / 120 +
        (1 / 2 : ℝ) ^ 6 * HTGeometry.gammaBoseMoment 5 4 -
          (((10 : ℝ) ^ 6)⁻¹ + ((9 : ℝ) ^ 6)⁻¹) := by
  rw [completedOddLogDerivMoment_two_ten_re_eq_resolved]
  norm_num [completedPrimeGammaResolvedMoment, completedPrimeFactorialMoment,
    completedGammaSpectralMoment, completedPolarPairMoment]

/-- One explicit negative value of the second moment falsifies the global right-even
factorization interface.  The positive endpoint is supplied unconditionally above. -/
theorem not_completedOddLogDerivPolynomialRightEvenFactorization_of_two_ten_neg
    (hneg : (completedOddLogDerivMoment (10 : ℂ) 2).re < 0) :
    ¬ CompletedOddLogDerivPolynomialRightEvenFactorization := by
  intro heven
  let f : ℝ → ℝ :=
    completedOddLogDerivPolynomialHankelReal
      (Polynomial.X : Polynomial ℝ)
  have hfac : HTGeometry.RealEvenFactorizationOn f (1 / 2) 10 := by
    simpa only [f, Polynomial.map_X] using
      heven (Polynomial.X : Polynomial ℤ) Polynomial.X_ne_zero 10 (by norm_num)
  have hleft : 0 < f (1 / 2) := by
    simpa only [f] using
      completedOddLogDerivPolynomialHankelReal_X_one_half_pos
  have hright : f 10 < 0 := by
    dsimp only [f]
    rw [completedOddLogDerivPolynomialHankelReal_X]
    simpa using hneg
  exact
    HTGeometry.not_realEvenFactorizationOn_of_left_pos_of_right_neg
      (by norm_num) hleft hright hfac

end

end RHTower
