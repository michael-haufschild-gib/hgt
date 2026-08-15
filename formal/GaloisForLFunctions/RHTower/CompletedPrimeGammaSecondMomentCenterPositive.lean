import GaloisForLFunctions.RHTower.CompletedPrimeGammaMomentFarRightAsymptotic
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation
import GaloisForLFunctions.RHTower.CompletedPrimeGammaResolvedMomentColligation
import GaloisForLFunctions.Hurwitz.ShiftedPowerTailAsymptotic
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

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

/-- The Gamma/Bose contribution at the far-right test point is a reciprocal sixth-power tail. -/
theorem gammaBoseMoment_five_four_eq_reciprocalSixth :
    HTGeometry.gammaBoseMoment 5 4 =
      ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + 5) ^ 6 := by
  unfold HTGeometry.gammaBoseMoment HTGeometry.gammaBoseWeight HTGeometry.gammaBoseNode
  apply tsum_congr
  intro j
  rw [← pow_add, inv_pow, one_div]

/-- The same Gamma/Bose contribution is the standard shifted sixth-power Hurwitz tail. -/
theorem gammaBoseMoment_five_four_eq_shiftedPowerTail :
    HTGeometry.gammaBoseMoment 5 4 =
      GaloisForLFunctions.shiftedPowerTail 5 5 := by
  apply Complex.ofReal_injective
  rw [HTGeometry.gammaBoseMoment_ofReal_eq_hzeta]
  simpa using
    (GaloisForLFunctions.hzeta_nat_ofReal_eq_shiftedPowerTail 5
      (x := (5 : ℝ)) (by positivity))

private theorem reciprocalSixth_eq_rpow (j : ℕ) :
    (1 : ℝ) / ((j : ℝ) + 5) ^ 6 =
      ((j + 5 : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
  push_cast
  rw [Real.rpow_neg (by positivity), one_div]
  change (((j : ℝ) + 5) ^ (6 : ℕ))⁻¹ = (((j : ℝ) + 5) ^ (6 : ℝ))⁻¹
  exact congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast ((j : ℝ) + 5) 6).symm

private theorem gammaBoseMoment_five_four_eq_head_eight_tail :
    HTGeometry.gammaBoseMoment 5 4 =
      (1 : ℝ) / 5 ^ 6 + 1 / 6 ^ 6 + 1 / 7 ^ 6 + 1 / 8 ^ 6 +
        1 / 9 ^ 6 + 1 / 10 ^ 6 + 1 / 11 ^ 6 + 1 / 12 ^ 6 +
        ∑' j : ℕ, ((j + 13 : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
  let f : ℕ → ℝ := fun j => (1 : ℝ) / ((j : ℝ) + 5) ^ 6
  have hsum : Summable f := by
    refine ((Real.summable_one_div_nat_add_rpow 5 6).mpr (by norm_num)).congr ?_
    intro j
    dsimp [f]
    rw [abs_of_pos (by positivity)]
    exact congrArg (fun t : ℝ => 1 / t) (Real.rpow_natCast ((j : ℝ) + 5) 6)
  have hsplit := hsum.sum_add_tsum_nat_add 8
  have htail :
      (∑' j : ℕ, f (j + 8)) =
        ∑' j : ℕ, ((j + 13 : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
    apply tsum_congr
    intro j
    simpa [f, Nat.add_assoc] using reciprocalSixth_eq_rpow (j + 8)
  rw [gammaBoseMoment_five_four_eq_reciprocalSixth]
  change (∑' j : ℕ, f j) = _
  rw [← hsplit, htail]
  norm_num [f, Finset.sum_range_succ]

/-- The completed Gamma contribution at `x = 10`, order two, is below its polar atom plus a
strict rational margin. -/
theorem completedGammaMoment_two_ten_lt :
    (1 / 2 : ℝ) ^ 6 * HTGeometry.gammaBoseMoment 5 4 <
      ((10 : ℝ) ^ 6)⁻¹ + 3 / 5000000 := by
  have htail := RHTower.Sieve.tsum_tail_rpow_neg_le
    (σ := (6 : ℝ)) (by norm_num) (L := 12) (by norm_num)
  have htail' :
      (∑' j : ℕ, ((j + 13 : ℕ) : ℝ) ^ (-(6 : ℝ))) ≤
        (12 : ℝ) ^ (1 - (6 : ℝ)) / ((6 : ℝ) - 1) := by
    calc
      (∑' j : ℕ, ((j + 13 : ℕ) : ℝ) ^ (-(6 : ℝ))) =
          ∑' j : ℕ, ((j + 12 + 1 : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
            apply tsum_congr
            intro j
            congr 2
      _ ≤ (12 : ℝ) ^ (1 - (6 : ℝ)) / ((6 : ℝ) - 1) := htail
  rw [gammaBoseMoment_five_four_eq_head_eight_tail]
  have hfac : 0 ≤ (1 / 2 : ℝ) ^ 6 := by positivity
  calc
    (1 / 2 : ℝ) ^ 6 *
        (1 / 5 ^ 6 + 1 / 6 ^ 6 + 1 / 7 ^ 6 + 1 / 8 ^ 6 +
          1 / 9 ^ 6 + 1 / 10 ^ 6 + 1 / 11 ^ 6 + 1 / 12 ^ 6 +
          ∑' j : ℕ, ((j + 13 : ℕ) : ℝ) ^ (-(6 : ℝ))) ≤
        (1 / 2 : ℝ) ^ 6 *
          (1 / 5 ^ 6 + 1 / 6 ^ 6 + 1 / 7 ^ 6 + 1 / 8 ^ 6 +
            1 / 9 ^ 6 + 1 / 10 ^ 6 + 1 / 11 ^ 6 + 1 / 12 ^ 6 +
            (12 : ℝ) ^ (1 - (6 : ℝ)) / ((6 : ℝ) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      linarith
    _ < ((10 : ℝ) ^ 6)⁻¹ + 3 / 5000000 := by norm_num

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

private theorem log_le_half_local {v : ℝ} (hv : 0 < v) : Real.log v ≤ v / 2 := by
  have hw : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
  have hwpos : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hlog : Real.log v = 2 * Real.log (Real.sqrt v) := by
    rw [Real.log_sqrt hv.le]
    ring
  have hstep : Real.log (Real.sqrt v) ≤ Real.sqrt v - 1 :=
    Real.log_le_sub_one_of_pos hwpos
  nlinarith [hlog.le, hlog.ge, hstep, sq_nonneg (Real.sqrt v - 2), hw]

private theorem log_le_sqrt_local {u : ℝ} (hu : 0 < u) : Real.log u ≤ Real.sqrt u := by
  have hs : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hlog : Real.log u = 2 * Real.log (Real.sqrt u) := by
    rw [Real.log_sqrt hu.le]
    ring
  have h := log_le_half_local hs
  linarith [hlog.le, hlog.ge, h]

private theorem rawAtom_nine_five_le_reciprocalSeventh (n : ℕ) :
    infiniteVonMangoldtGammaRawAtom 9 5 n ≤
      ((n + 2 : ℕ) : ℝ) ^ (-(7 : ℝ)) := by
  simp only [Nat.cast_add, Nat.cast_ofNat]
  let m : ℝ := (n : ℝ) + 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hmne : m ≠ 0 := hm.ne'
  have hmgt : (1 : ℝ) < m := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [m]
    linarith
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hmgt.le
  have hlam : ArithmeticFunction.vonMangoldt (n + 2) ≤ Real.log m := by
    simpa [m, Nat.cast_add] using ArithmeticFunction.vonMangoldt_le_log (n := n + 2)
  have hlogsqrt : Real.log m ≤ Real.sqrt m := log_le_sqrt_local hm
  have hnum : ArithmeticFunction.vonMangoldt (n + 2) * Real.log m ^ 5 ≤
      (Real.sqrt m) ^ 6 := by
    calc
      ArithmeticFunction.vonMangoldt (n + 2) * Real.log m ^ 5 ≤
          Real.log m * Real.log m ^ 5 :=
        mul_le_mul_of_nonneg_right hlam (pow_nonneg hlog 5)
      _ = Real.log m ^ 6 := by ring
      _ ≤ (Real.sqrt m) ^ 6 := pow_le_pow_left₀ hlog hlogsqrt 6
  have hexp : Real.exp (-9 * Real.log m) = (m ^ 9)⁻¹ := by
    rw [show -9 * Real.log m = -(((9 : ℕ) : ℝ) * Real.log m) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hm]
  have hrewrite : infiniteVonMangoldtGammaRawAtom 9 5 n =
      (ArithmeticFunction.vonMangoldt (n + 2) * Real.log m ^ 5) / m ^ 10 := by
    unfold infiniteVonMangoldtGammaRawAtom
    simp only [Nat.cast_add, Nat.cast_ofNat]
    change (ArithmeticFunction.vonMangoldt (n + 2) / m) *
      Real.exp (-9 * Real.log m) * Real.log m ^ 5 = _
    rw [hexp]
    field_simp [hmne]
  have hsix : (Real.sqrt m) ^ 6 = m ^ 3 := by
    calc
      (Real.sqrt m) ^ 6 = ((Real.sqrt m) ^ 2) ^ 3 := by ring
      _ = m ^ 3 := by rw [Real.sq_sqrt hm.le]
  have hden : 0 < m ^ 10 := pow_pos hm _
  have hrpow : m ^ (-(7 : ℝ)) = (m ^ 7)⁻¹ := by
    calc
      m ^ (-(7 : ℝ)) = (m ^ (7 : ℝ))⁻¹ := Real.rpow_neg hm.le 7
      _ = (m ^ 7)⁻¹ := congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast m 7)
  rw [hrewrite]
  calc
    (ArithmeticFunction.vonMangoldt (n + 2) * Real.log m ^ 5) / m ^ 10 ≤
        (Real.sqrt m) ^ 6 / m ^ 10 := div_le_div_of_nonneg_right hnum hden.le
    _ = m ^ (-(7 : ℝ)) := by
      rw [hsix, hrpow]
      field_simp [hmne]

private theorem rawAtom_nine_five_le_of_log_le (n : ℕ) {B : ℝ}
    (hlogB : Real.log ((n : ℝ) + 2) ≤ B) :
    infiniteVonMangoldtGammaRawAtom 9 5 n ≤ B ^ 6 / ((n : ℝ) + 2) ^ 10 := by
  let m : ℝ := (n : ℝ) + 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hmne : m ≠ 0 := hm.ne'
  have hmgt : (1 : ℝ) < m := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [m]
    linarith
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hmgt.le
  have hlam : ArithmeticFunction.vonMangoldt (n + 2) ≤ Real.log m := by
    simpa [m, Nat.cast_add] using ArithmeticFunction.vonMangoldt_le_log (n := n + 2)
  have hexp : Real.exp (-9 * Real.log m) = (m ^ 9)⁻¹ := by
    rw [show -9 * Real.log m = -(((9 : ℕ) : ℝ) * Real.log m) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hm]
  have hrewrite : infiniteVonMangoldtGammaRawAtom 9 5 n =
      (ArithmeticFunction.vonMangoldt (n + 2) * Real.log m ^ 5) / m ^ 10 := by
    unfold infiniteVonMangoldtGammaRawAtom
    simp only [Nat.cast_add, Nat.cast_ofNat]
    change (ArithmeticFunction.vonMangoldt (n + 2) / m) *
      Real.exp (-9 * Real.log m) * Real.log m ^ 5 = _
    rw [hexp]
    field_simp [hmne]
  have hnum : ArithmeticFunction.vonMangoldt (n + 2) * Real.log m ^ 5 ≤ B ^ 6 := by
    calc
      ArithmeticFunction.vonMangoldt (n + 2) * Real.log m ^ 5 ≤
          Real.log m * Real.log m ^ 5 :=
        mul_le_mul_of_nonneg_right hlam (pow_nonneg hlog 5)
      _ = Real.log m ^ 6 := by ring
      _ ≤ B ^ 6 := by
        simpa [m] using pow_le_pow_left₀ hlog hlogB 6
  have hden : 0 < m ^ 10 := pow_pos hm _
  rw [hrewrite]
  exact div_le_div_of_nonneg_right hnum hden.le

private theorem log_two_le_347_div_500 : Real.log (2 : ℝ) ≤ 347 / 500 := by
  nlinarith [Real.log_two_lt_d9]

private theorem log_three_le_11_div_10 : Real.log (3 : ℝ) ≤ 11 / 10 := by
  nlinarith [Real.log_three_lt_d9]

private theorem log_three_le_1099_div_1000 : Real.log (3 : ℝ) ≤ 1099 / 1000 := by
  nlinarith [Real.log_three_lt_d9]

private theorem log_five_le_161_div_100 : Real.log (5 : ℝ) ≤ 161 / 100 := by
  nlinarith [Real.log_five_lt_d9]

private theorem log_four_le_347_div_250 : Real.log (4 : ℝ) ≤ 347 / 250 := by
  rw [Real.log_four_eq]
  linarith [log_two_le_347_div_500]

private theorem log_six_le_1793_div_1000 : Real.log (6 : ℝ) ≤ 1793 / 1000 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [log_two_le_347_div_500, log_three_le_1099_div_1000]

private theorem log_seven_le_eight_div_three : Real.log (7 : ℝ) ≤ 8 / 3 := by
  calc
    Real.log (7 : ℝ) ≤ Real.sqrt 7 := log_le_sqrt_local (by norm_num)
    _ ≤ 8 / 3 := by
      rw [Real.sqrt_le_iff]
      norm_num

private theorem log_eight_le_521_div_250 : Real.log (8 : ℝ) ≤ 521 / 250 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  linarith [log_two_le_347_div_500]

private theorem log_nine_le_11_div_5 : Real.log (9 : ℝ) ≤ 11 / 5 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  linarith [log_three_le_11_div_10]

private theorem log_ten_le_231_div_100 : Real.log (10 : ℝ) ≤ 231 / 100 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [log_two_le_347_div_500, log_five_le_161_div_100]

private theorem rawEulerHead_nine_five_lt :
    (∑ n ∈ Finset.range 9, infiniteVonMangoldtGammaRawAtom 9 5 n) / 120 <
      127 / 100000000 := by
  have h0 : infiniteVonMangoldtGammaRawAtom 9 5 0 ≤
      (347 / 500 : ℝ) ^ 6 / 2 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 0 (B := (347 / 500 : ℝ))
      (by
        convert log_two_le_347_div_500 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h1 : infiniteVonMangoldtGammaRawAtom 9 5 1 ≤
      (11 / 10 : ℝ) ^ 6 / 3 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 1 (B := (11 / 10 : ℝ))
      (by
        convert log_three_le_11_div_10 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h2 : infiniteVonMangoldtGammaRawAtom 9 5 2 ≤
      (347 / 250 : ℝ) ^ 6 / 4 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 2 (B := (347 / 250 : ℝ))
      (by
        convert log_four_le_347_div_250 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h3 : infiniteVonMangoldtGammaRawAtom 9 5 3 ≤
      (161 / 100 : ℝ) ^ 6 / 5 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 3 (B := (161 / 100 : ℝ))
      (by
        convert log_five_le_161_div_100 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h4 : infiniteVonMangoldtGammaRawAtom 9 5 4 ≤
      (1793 / 1000 : ℝ) ^ 6 / 6 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 4 (B := (1793 / 1000 : ℝ))
      (by
        convert log_six_le_1793_div_1000 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h5 : infiniteVonMangoldtGammaRawAtom 9 5 5 ≤
      (8 / 3 : ℝ) ^ 6 / 7 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 5 (B := (8 / 3 : ℝ))
      (by
        convert log_seven_le_eight_div_three using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h6 : infiniteVonMangoldtGammaRawAtom 9 5 6 ≤
      (521 / 250 : ℝ) ^ 6 / 8 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 6 (B := (521 / 250 : ℝ))
      (by
        convert log_eight_le_521_div_250 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h7 : infiniteVonMangoldtGammaRawAtom 9 5 7 ≤
      (11 / 5 : ℝ) ^ 6 / 9 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 7 (B := (11 / 5 : ℝ))
      (by
        convert log_nine_le_11_div_5 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  have h8 : infiniteVonMangoldtGammaRawAtom 9 5 8 ≤
      (231 / 100 : ℝ) ^ 6 / 10 ^ 10 := by
    convert rawAtom_nine_five_le_of_log_le 8 (B := (231 / 100 : ℝ))
      (by
        convert log_ten_le_231_div_100 using 1
        all_goals norm_num) using 1
    all_goals norm_num
  calc
    (∑ n ∈ Finset.range 9, infiniteVonMangoldtGammaRawAtom 9 5 n) / 120 =
        (infiniteVonMangoldtGammaRawAtom 9 5 0 +
          infiniteVonMangoldtGammaRawAtom 9 5 1 +
          infiniteVonMangoldtGammaRawAtom 9 5 2 +
          infiniteVonMangoldtGammaRawAtom 9 5 3 +
          infiniteVonMangoldtGammaRawAtom 9 5 4 +
          infiniteVonMangoldtGammaRawAtom 9 5 5 +
          infiniteVonMangoldtGammaRawAtom 9 5 6 +
          infiniteVonMangoldtGammaRawAtom 9 5 7 +
          infiniteVonMangoldtGammaRawAtom 9 5 8) / 120 := by
      norm_num [Finset.sum_range_succ]
    _ ≤ ((347 / 500 : ℝ) ^ 6 / 2 ^ 10 +
          (11 / 10 : ℝ) ^ 6 / 3 ^ 10 +
          (347 / 250 : ℝ) ^ 6 / 4 ^ 10 +
          (161 / 100 : ℝ) ^ 6 / 5 ^ 10 +
          (1793 / 1000 : ℝ) ^ 6 / 6 ^ 10 +
          (8 / 3 : ℝ) ^ 6 / 7 ^ 10 +
          (521 / 250 : ℝ) ^ 6 / 8 ^ 10 +
          (11 / 5 : ℝ) ^ 6 / 9 ^ 10 +
          (231 / 100 : ℝ) ^ 6 / 10 ^ 10) / 120 := by
      apply div_le_div_of_nonneg_right
      · linarith
      · norm_num
    _ < 127 / 100000000 := by norm_num

private theorem rawEulerTail_nine_five_le :
    ∑' j : ℕ, infiniteVonMangoldtGammaRawAtom 9 5 (j + 9) ≤
      ∑' j : ℕ, (((j + 11 : ℕ) : ℝ)) ^ (-(7 : ℝ)) := by
  have hraw : Summable (fun j : ℕ => infiniteVonMangoldtGammaRawAtom 9 5 (j + 9)) :=
    (summable_nat_add_iff 9).mpr
      (summable_infiniteVonMangoldtGammaRawAtom (by norm_num) 5)
  have hpow : Summable (fun j : ℕ => (((j + 11 : ℕ) : ℝ)) ^ (-(7 : ℝ))) :=
    (summable_nat_add_iff 11).mpr
      (Real.summable_nat_rpow.mpr (by norm_num))
  refine Summable.tsum_le_tsum (fun j => ?_) hraw hpow
  simpa [Nat.add_assoc] using rawAtom_nine_five_le_reciprocalSeventh (j + 9)

private theorem rawEulerTail_nine_five_le_one_div_sixMillion :
    ∑' j : ℕ, infiniteVonMangoldtGammaRawAtom 9 5 (j + 9) ≤
      1 / 6000000 := by
  calc
    (∑' j : ℕ, infiniteVonMangoldtGammaRawAtom 9 5 (j + 9)) ≤
        ∑' j : ℕ, (((j + 11 : ℕ) : ℝ)) ^ (-(7 : ℝ)) := rawEulerTail_nine_five_le
    _ = ∑' j : ℕ, (((j + 10 + 1 : ℕ) : ℝ)) ^ (-(7 : ℝ)) := by
      apply tsum_congr
      intro j
      congr 2
    _ ≤ (10 : ℝ) ^ (1 - (7 : ℝ)) / ((7 : ℝ) - 1) :=
      RHTower.Sieve.tsum_tail_rpow_neg_le (σ := (7 : ℝ)) (by norm_num)
        (L := 10) (by norm_num)
    _ = 1 / 6000000 := by norm_num

/-- A dependency-closed upper certificate for the Euler contribution at the far-right test
point.  This is the quantitative positive survivor exposed by the failed factorization route. -/
theorem completedEulerMoment_two_ten_lt :
    infiniteVonMangoldtGammaRawMoment 9 5 / 120 <
      127 / 100000000 + 1 / 720000000 := by
  have hsum := (summable_infiniteVonMangoldtGammaRawAtom (x := (9 : ℝ))
    (by norm_num) 5).sum_add_tsum_nat_add 9
  have htail : (∑' j : ℕ, infiniteVonMangoldtGammaRawAtom 9 5 (j + 9)) / 120 ≤
      1 / 720000000 := by
    calc
      (∑' j : ℕ, infiniteVonMangoldtGammaRawAtom 9 5 (j + 9)) / 120 ≤
          (1 / 6000000 : ℝ) / 120 :=
        div_le_div_of_nonneg_right rawEulerTail_nine_five_le_one_div_sixMillion (by norm_num)
      _ = 1 / 720000000 := by norm_num
  rw [infiniteVonMangoldtGammaRawMoment, ← hsum]
  calc
    ((∑ n ∈ Finset.range 9, infiniteVonMangoldtGammaRawAtom 9 5 n) +
        ∑' j : ℕ, infiniteVonMangoldtGammaRawAtom 9 5 (j + 9)) / 120 =
        (∑ n ∈ Finset.range 9, infiniteVonMangoldtGammaRawAtom 9 5 n) / 120 +
          (∑' j : ℕ, infiniteVonMangoldtGammaRawAtom 9 5 (j + 9)) / 120 := by ring
    _ < 127 / 100000000 + 1 / 720000000 :=
      add_lt_add_of_lt_of_le rawEulerHead_nine_five_lt htail

/-- The paper's far-right second completed moment is strictly negative, unconditionally. -/
theorem completedOddLogDerivMoment_two_ten_re_neg :
    (completedOddLogDerivMoment (10 : ℂ) 2).re < 0 := by
  rw [completedOddLogDerivMoment_two_ten_re_eq_source]
  have hEuler := completedEulerMoment_two_ten_lt
  have hGamma := completedGammaMoment_two_ten_lt
  calc
    infiniteVonMangoldtGammaRawMoment 9 5 / 120 +
        (1 / 2 : ℝ) ^ 6 * HTGeometry.gammaBoseMoment 5 4 -
          (((10 : ℝ) ^ 6)⁻¹ + ((9 : ℝ) ^ 6)⁻¹) <
        (127 / 100000000 + 1 / 720000000) +
          (((10 : ℝ) ^ 6)⁻¹ + 3 / 5000000) -
            (((10 : ℝ) ^ 6)⁻¹ + ((9 : ℝ) ^ 6)⁻¹) := by
      linarith
    _ < 0 := by norm_num

/-- The global right-even factorization interface is false at the certified test point. -/
theorem not_completedOddLogDerivPolynomialRightEvenFactorization :
    ¬ CompletedOddLogDerivPolynomialRightEvenFactorization :=
  not_completedOddLogDerivPolynomialRightEvenFactorization_of_two_ten_neg
    completedOddLogDerivMoment_two_ten_re_neg

end

end RHTower
