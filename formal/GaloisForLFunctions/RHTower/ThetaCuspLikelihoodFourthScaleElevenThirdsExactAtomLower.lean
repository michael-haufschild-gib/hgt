import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalTailCoolingElevenThirds

/-!
# Exact scale-11/3 fourth atom-ray producer

The constant leading-monomial comparison loses the positive continuous-ray surplus and cannot
close the next D1 chamber. This module evaluates the literal fourth score on the dominant mixed
atom-ray carrier. The exact ray surplus proves `1300 - 336A < J₄` on
`11/3 ≤ A ≤ 59/16`, continuing the preceding affine profile without a seam loss.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact rational fourth-score factor after extracting `exp(-3A)`. -/
def thetaCuspLikelihoodFourthExactDominantPolynomial (A B : ℝ) : ℝ :=
  16 * thetaLikelihoodFourthScore (3 * A) + 18 *
    (A ^ 4 * (81 / B + 108 / B ^ 2 + 108 / B ^ 3 + 72 / B ^ 4 + 24 / B ^ 5) -
      6 * A ^ 3 * (27 / B + 27 / B ^ 2 + 18 / B ^ 3 + 6 / B ^ 4) +
      7 * A ^ 2 * (9 / B + 6 / B ^ 2 + 2 / B ^ 3) -
      A * (3 / B + 1 / B ^ 2))

/-- Chamber-coordinate specialization of the exact dominant fourth-score factor. -/
def thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial (d : ℝ) : ℝ :=
  thetaCuspLikelihoodFourthExactDominantPolynomial (11 / 3 + d) (13 / 6 + d)

/-- The exact support-edge ratio for the fourth score at `z=11`. -/
theorem sixHundredEightyOneOverThirteenHundredThirtyOne_mul_pow_four_le_fourthScore_of_eleven_le
    {z : ℝ} (hz : (11 : ℝ) ≤ z) :
    (681 / 1331 : ℝ) * z ^ 4 ≤ thetaLikelihoodFourthScore z := by
  let y := z - 11
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  rw [show z = 11 + y by dsimp only [y]; ring]
  dsimp [thetaLikelihoodFourthScore]
  ring_nf
  have hy2 : 0 ≤ y ^ 2 := by positivity
  have hy3 : 0 ≤ y ^ 3 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  nlinarith

private theorem integrable_thetaLikelihoodFourthScore_mul_exp_higher
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  have h4 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul (A ^ 4)
  have h3 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
      (6 * A ^ 3)
  have h2 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
      (7 * A ^ 2)
  have h1 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul A
  convert (((h4.sub h3).add h2).sub h1) using 1
  funext t
  dsimp [thetaLikelihoodFourthScore]
  ring

private theorem integral_thetaLikelihoodFourthScore_mul_exp_higher_eq
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
      ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        6 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        7 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h4 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul (A ^ 4)
  have h3 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
      (6 * A ^ 3)
  have h2 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
      (7 * A ^ 2)
  have h1 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ 4 * (t ^ 4 * Real.exp (-B * t))
  let f3 : ℝ → ℝ := fun t => (6 * A ^ 3) * (t ^ 3 * Real.exp (-B * t))
  let f2 : ℝ → ℝ := fun t => (7 * A ^ 2) * (t ^ 2 * Real.exp (-B * t))
  let f1 : ℝ → ℝ := fun t => A * (t ^ 1 * Real.exp (-B * t))
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))) =
      ((f4 - f3) + f2) - f1 by
    funext t
    dsimp [thetaLikelihoodFourthScore, f4, f3, f2, f1]
    ring]
  rw [integral_sub' ((h4.sub h3).add h2) h1,
    integral_add' (h4.sub h3) h2, integral_sub' h4 h3]
  simp only [integral_const_mul]
  rw [← thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    ← thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    ← thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    ← thetaCuspHigherLikelihoodSpectralMoment_eq_integral]

/-- Literal dominant atom-ray fourth score equals the exact rational factor times `exp(-3A)`. -/
theorem integral_thetaLikelihoodFourthScore_dominantAtom_eq_scale11Over3_exact
    (A : ℝ) {B : ℝ} (hAlo : (11 / 3 : ℝ) ≤ A) (_hAhi : A ≤ 59 / 16)
    (hBA : B = A - 3 / 2) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2) =
      Real.exp (-(3 * A)) *
        thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial (A - 11 / 3) := by
  have hB : 0 < B := by rw [hBA]; linarith
  let d := A - 11 / 3
  have hAeq : A = 11 / 3 + d := by dsimp only [d]; ring
  have hBeq : B = 13 / 6 + d := by rw [hBA, hAeq]; ring
  have hextract :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) = Real.exp (-(3 * A)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  have hMeasure : thetaCuspAtomLikelihoodSpectralMeasure 2 ≤
      thetaCuspHigherLikelihoodSpectralMeasure := by
    rw [thetaCuspHigherLikelihoodSpectralMeasure]
    simpa only [Nat.zero_add] using
      Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0
  have h4 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).mono_measure
      hMeasure).const_mul (A ^ 4)
  have h3 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).mono_measure
      hMeasure).const_mul (6 * A ^ 3)
  have h2 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).mono_measure
      hMeasure).const_mul (7 * A ^ 2)
  have h1 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).mono_measure
      hMeasure).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ 4 * (t ^ 4 * Real.exp (-B * t))
  let f3 : ℝ → ℝ := fun t => (6 * A ^ 3) * (t ^ 3 * Real.exp (-B * t))
  let f2 : ℝ → ℝ := fun t => (7 * A ^ 2) * (t ^ 2 * Real.exp (-B * t))
  let f1 : ℝ → ℝ := fun t => A * (t ^ 1 * Real.exp (-B * t))
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))) =
      ((f4 - f3) + f2) - f1 by
    funext t
    dsimp [thetaLikelihoodFourthScore, f4, f3, f2, f1]
    ring]
  rw [integral_sub' ((h4.sub h3).add h2) h1,
    integral_add' (h4.sub h3) h2, integral_sub' h4 h3]
  simp only [integral_const_mul]
  simp only [neg_mul]
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 4 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 3 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 2 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 1 hB]
  norm_num [thetaCuspLikelihoodGap, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  rw [show B * 3 = 3 * B by ring]
  rw [hextract]
  calc
    _ = Real.exp (-(3 * A)) * thetaCuspLikelihoodFourthExactDominantPolynomial A B := by
      dsimp [thetaCuspLikelihoodFourthExactDominantPolynomial, thetaLikelihoodFourthScore]
      ring
    _ = Real.exp (-(3 * A)) *
        thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial d := by
      rw [hAeq, hBeq]
      rfl
    _ = Real.exp (-(3 * A)) *
        thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial (A - 11 / 3) := by
      rfl

/-- Rational lower enclosure for `exp(-11)`. -/
theorem oneOverSixtyThousand_lt_exp_neg_eleven :
    (1 / 60000 : ℝ) < Real.exp (-11) := by
  have hpow11 : Real.exp 1 ^ 11 < (2.7182818286 : ℝ) ^ 11 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h11 : Real.exp 11 < (60000 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hprod : Real.exp (-11) * Real.exp 11 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_lt_mul_of_pos_left h11 (Real.exp_pos (-11))
  rw [hprod] at hmul
  nlinarith

/-- Live lower exponential envelope on `11/3 ≤ A ≤ 59/16`. -/
theorem thetaCuspLikelihoodFourthScale11Over3_expAffine_lt_exp_neg_three_mul
    {A : ℝ} (hAlo : (11 / 3 : ℝ) ≤ A) (hAhi : A ≤ 59 / 16) :
    (1 / 60000 : ℝ) * (1 - 3 * (A - 11 / 3)) < Real.exp (-3 * A) := by
  let d := A - 11 / 3
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d]; linarith
  have hfactor : 0 < 1 - 3 * d := by linarith
  have hfirst : (1 / 60000 : ℝ) * (1 - 3 * d) <
      Real.exp (-11) * (1 - 3 * d) :=
    mul_lt_mul_of_pos_right oneOverSixtyThousand_lt_exp_neg_eleven hfactor
  have hlinear : 1 - 3 * d ≤ Real.exp (-(3 * d)) := Real.one_sub_le_exp_neg (3 * d)
  calc
    (1 / 60000 : ℝ) * (1 - 3 * (A - 11 / 3)) =
        (1 / 60000 : ℝ) * (1 - 3 * d) := by rfl
    _ < Real.exp (-11) * (1 - 3 * d) := hfirst
    _ ≤ Real.exp (-11) * Real.exp (-(3 * d)) := by gcongr
    _ = Real.exp (-3 * A) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring

set_option maxHeartbeats 6000000 in
/-- Cleared exact-ray certificate for the continued affine fourth floor. -/
theorem exactFourth11Over3AffineFloor_lt_atomEnvelope
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 48) :
    (1000 / 989 : ℝ) * (68 - 336 * d) <
      16 * (399 / 400 : ℝ) *
        ((1 / 60000 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial d := by
  have hB : 0 < 13 / 6 + d := by linarith
  have hmul : (13 / 6 + d) ^ 5 *
      ((1000 / 989 : ℝ) * (68 - 336 * d)) <
    (13 / 6 + d) ^ 5 *
      (16 * (399 / 400 : ℝ) *
        ((1 / 60000 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial d) := by
    dsimp [thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial,
      thetaCuspLikelihoodFourthExactDominantPolynomial, thetaLikelihoodFourthScore]
    field_simp [hB.ne']
    ring_nf
    rw [← sub_pos]
    ring_nf
    have hd2 : d ^ 2 ≤ (1 / 48 : ℝ) ^ 2 := pow_le_pow_left₀ hd hdhi 2
    have hd3 : d ^ 3 ≤ (1 / 48 : ℝ) ^ 3 := pow_le_pow_left₀ hd hdhi 3
    have hd4 : d ^ 4 ≤ (1 / 48 : ℝ) ^ 4 := pow_le_pow_left₀ hd hdhi 4
    have hd5 : d ^ 5 ≤ (1 / 48 : ℝ) ^ 5 := pow_le_pow_left₀ hd hdhi 5
    have hd6 : d ^ 6 ≤ (1 / 48 : ℝ) ^ 6 := pow_le_pow_left₀ hd hdhi 6
    have hd7 : d ^ 7 ≤ (1 / 48 : ℝ) ^ 7 := pow_le_pow_left₀ hd hdhi 7
    have hd8 : d ^ 8 ≤ (1 / 48 : ℝ) ^ 8 := pow_le_pow_left₀ hd hdhi 8
    have hd9 : d ^ 9 ≤ (1 / 48 : ℝ) ^ 9 := pow_le_pow_left₀ hd hdhi 9
    have hd10 : d ^ 10 ≤ (1 / 48 : ℝ) ^ 10 := pow_le_pow_left₀ hd hdhi 10
    have hd11 : d ^ 11 ≤ (1 / 48 : ℝ) ^ 11 := pow_le_pow_left₀ hd hdhi 11
    have hd12 : d ^ 12 ≤ (1 / 48 : ℝ) ^ 12 := pow_le_pow_left₀ hd hdhi 12
    have hd13 : 0 ≤ d ^ 13 := by positivity
    norm_num at hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 ⊢
    nlinarith
  nlinarith [pow_pos hB 5]

/-- The exact dominant atom-ray score proves the continued ordinary fourth floor. -/
theorem oneThousandOverNineHundredEightyNine_mul_fourth11Over3AffineFloor_lt_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (11 / 3 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 59 / 16) :
    (1000 / 989 : ℝ) *
        (1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x) <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let d := A - 11 / 3
  let atomFloor := (1 / 60000 : ℝ) * (1 - 3 * d) *
    thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial d
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd : 0 ≤ d := by dsimp only [d, A] at hAlo ⊢; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d, A] at hAhi ⊢; linarith
  have hPolyPos : 0 < thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial d := by
    have hcert := exactFourth11Over3AffineFloor_lt_atomEnvelope hd hdhi
    have hlinear : 0 < 1 - 3 * d := by linarith
    have hprofile : 0 < 68 - 336 * d := by linarith
    have hleft : 0 < (1000 / 989 : ℝ) * (68 - 336 * d) := by
      positivity
    have hprod : 0 <
        (16 * (399 / 400 : ℝ) * ((1 / 60000 : ℝ) * (1 - 3 * d))) *
          thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial d := by
      nlinarith
    have hfactor : 0 <
        16 * (399 / 400 : ℝ) * ((1 / 60000 : ℝ) * (1 - 3 * d)) := by
      positivity
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hfactor.le hneg.1).elim
  have hExp := thetaCuspLikelihoodFourthScale11Over3_expAffine_lt_exp_neg_three_mul
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hExp' : (1 / 60000 : ℝ) * (1 - 3 * (A - 11 / 3)) <
      Real.exp (-(3 * A)) := by
    simpa only [A, neg_mul] using hExp
  have hAtomEq := integral_thetaLikelihoodFourthScore_dominantAtom_eq_scale11Over3_exact
    A (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hAtom : atomFloor <
      ∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
    rw [hAtomEq]
    dsimp only [atomFloor, d]
    exact mul_lt_mul_of_pos_right hExp' hPolyPos
  have hMeasure : thetaCuspAtomLikelihoodSpectralMeasure 2 ≤
      thetaCuspHigherLikelihoodSpectralMeasure := by
    rw [thetaCuspHigherLikelihoodSpectralMeasure]
    simpa only [Nat.zero_add] using
      Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0
  have hInt := integrable_thetaLikelihoodFourthScore_mul_exp_higher A hB
  have hMono :
      (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspAtomLikelihoodSpectralMeasure 2) ≤
        ∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure := by
    apply integral_mono_measure hMeasure
    · filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
      have hAt : (11 : ℝ) ≤ A * t := by
        have hA0 : 0 ≤ A := by dsimp only [A] at hAlo ⊢; linarith
        nlinarith [mul_le_mul hAlo ht (by norm_num : (0 : ℝ) ≤ 3) hA0]
      have hscore :=
        sixHundredEightyOneOverThirteenHundredThirtyOne_mul_pow_four_le_fourthScore_of_eleven_le
          hAt
      have hscore0 : 0 ≤ thetaLikelihoodFourthScore (A * t) := by
        exact (by positivity : (0 : ℝ) ≤ (681 / 1331 : ℝ) * (A * t) ^ 4).trans hscore
      exact mul_nonneg hscore0 (Real.exp_pos (-(B * t))).le
    · exact hInt
  have hTotal : atomFloor <
      ∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure := hAtom.trans_le hMono
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  let p := thetaCuspLikelihoodTailProbability B
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have hpEq : p = 1 - 1 / P := by
    have hPartEq := thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB
    have hden : 1 + thetaCuspHigherLikelihoodSpectralMoment B 0 ≠ 0 := by
      rw [← hPartEq]
      exact (by simpa only [P] using hP.ne')
    dsimp only [p, P, thetaCuspLikelihoodTailProbability,
      thetaCuspLikelihoodNormalizedMoment]
    rw [hPartEq]
    field_simp [hden]
    ring
  have hPinv : (399 / 400 : ℝ) < 1 / P := by
    rw [hpEq] at hpSmall
    linarith
  have hfloor : 0 < atomFloor := by
    have hfactor : 0 < 1 - 3 * d := by linarith
    dsimp only [atomFloor]
    positivity
  have hNorm : 16 * (399 / 400 : ℝ) * atomFloor <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
    have hfirst := mul_lt_mul_of_pos_right hPinv hfloor
    have hsecond := mul_lt_mul_of_pos_left hTotal (by positivity : (0 : ℝ) < 1 / P)
    have hIntegralEq := integral_thetaLikelihoodFourthScore_mul_exp_higher_eq A hB
    calc
      16 * (399 / 400 : ℝ) * atomFloor < 16 * ((1 / P) * atomFloor) := by
        nlinarith
      _ < 16 * ((1 / P) *
          (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
            ∂thetaCuspHigherLikelihoodSpectralMeasure)) := by gcongr
      _ = thetaCuspLikelihoodSourceOrdinaryJetFour x := by
        rw [hIntegralEq]
        dsimp only [A, B]
        unfold thetaCuspLikelihoodSourceOrdinaryJetFour
          thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
        dsimp only [P]
        field_simp [hP.ne']
        ring
  have hpoly := exactFourth11Over3AffineFloor_lt_atomEnvelope hd hdhi
  have hprofile : 1300 - 336 * A = 68 - 336 * d := by dsimp only [d]; ring
  rw [show thetaCuspSingleAtomReflectionScale 1 x = A by rfl, hprofile]
  exact hpoly.trans (by simpa only [atomFloor, mul_assoc] using hNorm)

/-- Logarithmic fourth-jet floor on `11/3 ≤ A ≤ 59/16`. -/
theorem fourth11Over3AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (11 / 3 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 59 / 16) :
    1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord :=
    oneThousandOverNineHundredEightyNine_mul_fourth11Over3AffineFloor_lt_ordinaryJetFour
      hx hAlo hAhi
  have hretain :=
    nineHundredEightyNineThousandths_mul_ordinaryJetFour_lt_logJetFour_of_11Over3_le hx hAlo
  calc
    1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x =
        (989 / 1000 : ℝ) * ((1000 / 989 : ℝ) *
          (1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ < (989 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

/-- Weight-coordinate form of the exact scale-`11/3` fourth producer. -/
theorem fourth11Over3AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (11 / 3 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 59 / 16) :
    796 - 336 * thetaCuspBornWittenWeight 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have h := fourth11Over3AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    hx hAlo hAhi
  convert h using 1
  dsimp [thetaCuspSingleAtomReflectionScale]
  rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
  norm_num
  rw [show 2 * x = x + x by ring, Real.exp_add]
  ring

end
end RHTower
