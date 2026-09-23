import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingOneHundredSeventyFiveFortyEighths
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthScaleElevenThirdsExactAtomLower

/-!
# Exact scale-175/48 fourth atom-ray producer

The constant leading-monomial comparison loses the positive continuous-ray surplus and cannot
close the next D1 chamber. This module evaluates the literal fourth score on the dominant mixed
atom-ray carrier. The exact ray surplus proves `772 - 192A < J₄` on
`11/3 ≤ A ≤ 59/16`, continuing the preceding affine profile without a seam loss.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Chamber-coordinate specialization of the exact dominant fourth-score factor. -/
def thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial (d : ℝ) : ℝ :=
  thetaCuspLikelihoodFourthExactDominantPolynomial (175 / 48 + d) (103 / 48 + d)

/-- The exact support-edge ratio for the fourth score at \`z = 175/16\`. -/
theorem oneHalf_mul_pow_four_le_fourthScore_of_oneHundredSeventyFiveSixteenths_le
    {z : ℝ} (hz : (175 / 16 : ℝ) ≤ z) :
    (1 / 2 : ℝ) * z ^ (4 : ℕ) ≤ thetaLikelihoodFourthScore z := by
  let y := z - 175 / 16
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  rw [show z = 175 / 16 + y by dsimp only [y]; ring]
  dsimp [thetaLikelihoodFourthScore]
  ring_nf
  have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  nlinarith

private theorem integrable_thetaLikelihoodFourthScore_mul_exp_higher
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  have h4 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul (A ^ (4 : ℕ))
  have h3 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
      (6 * A ^ (3 : ℕ))
  have h2 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
      (7 * A ^ (2 : ℕ))
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
      A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        6 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        7 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h4 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul (A ^ (4 : ℕ))
  have h3 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
      (6 * A ^ (3 : ℕ))
  have h2 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
      (7 * A ^ (2 : ℕ))
  have h1 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ (4 : ℕ) * (t ^ (4 : ℕ) * Real.exp (-B * t))
  let f3 : ℝ → ℝ := fun t => (6 * A ^ (3 : ℕ)) * (t ^ (3 : ℕ) * Real.exp (-B * t))
  let f2 : ℝ → ℝ := fun t => (7 * A ^ (2 : ℕ)) * (t ^ (2 : ℕ) * Real.exp (-B * t))
  let f1 : ℝ → ℝ := fun t => A * (t ^ (1 : ℕ) * Real.exp (-B * t))
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
theorem integral_thetaLikelihoodFourthScore_dominantAtom_eq_scale175Over48_exact
    (A : ℝ) {B : ℝ} (hAlo : (175 / 48 : ℝ) ≤ A) (_hAhi : A ≤ 11 / 3)
    (hBA : B = A - 3 / 2) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2) =
      Real.exp (-(3 * A)) *
        thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial (A - 175 / 48) := by
  have hB : 0 < B := by rw [hBA]; linarith
  let d := A - 175 / 48
  have hAeq : A = 175 / 48 + d := by dsimp only [d]; ring
  have hBeq : B = 103 / 48 + d := by rw [hBA, hAeq]; ring
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
      hMeasure).const_mul (A ^ (4 : ℕ))
  have h3 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).mono_measure
      hMeasure).const_mul (6 * A ^ (3 : ℕ))
  have h2 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).mono_measure
      hMeasure).const_mul (7 * A ^ (2 : ℕ))
  have h1 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).mono_measure
      hMeasure).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ (4 : ℕ) * (t ^ (4 : ℕ) * Real.exp (-B * t))
  let f3 : ℝ → ℝ := fun t => (6 * A ^ (3 : ℕ)) * (t ^ (3 : ℕ) * Real.exp (-B * t))
  let f2 : ℝ → ℝ := fun t => (7 * A ^ (2 : ℕ)) * (t ^ (2 : ℕ) * Real.exp (-B * t))
  let f1 : ℝ → ℝ := fun t => A * (t ^ (1 : ℕ) * Real.exp (-B * t))
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
        thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial d := by
      rw [hAeq, hBeq]
      rfl
    _ = Real.exp (-(3 * A)) *
        thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial (A - 175 / 48) := by
      rfl

/-- Rational lower enclosure for \`exp(-175/16)\`. -/
theorem oneOverFiftySixThousandFiveHundred_lt_exp_neg_oneHundredSeventyFiveSixteenths :
    (1 / 56500 : ℝ) < Real.exp (-(175 / 16 : ℝ)) := by
  have hpow11 : Real.exp 1 ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h11 : Real.exp 11 < (59875 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hsmall : Real.exp (-(1 / 16 : ℝ)) ≤ 16 / 17 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) 2
    have hpos := Real.exp_pos (-(1 / 16 : ℝ))
    have hprod : Real.exp (-(1 / 16 : ℝ)) * Real.exp (1 / 16 : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    nlinarith
  have h175 : Real.exp (175 / 16 : ℝ) < 56500 := by
    rw [show (175 / 16 : ℝ) = 11 + (-(1 / 16 : ℝ)) by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 11]
  have hprod : Real.exp (-(175 / 16 : ℝ)) * Real.exp (175 / 16 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(175 / 16 : ℝ))]

/-- Live lower exponential envelope on \`175/48 ≤ A ≤ 11/3\`. -/
theorem thetaCuspLikelihoodFourthScale175Over48_expAffine_lt_exp_neg_three_mul
    {A : ℝ} (hAlo : (175 / 48 : ℝ) ≤ A) (hAhi : A ≤ 11 / 3) :
    (1 / 56500 : ℝ) * (1 - 3 * (A - 175 / 48)) < Real.exp (-3 * A) := by
  let d := A - 175 / 48
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d]; linarith
  have hfactor : 0 < 1 - 3 * d := by linarith
  have hfirst : (1 / 56500 : ℝ) * (1 - 3 * d) <
      Real.exp (-(175 / 16 : ℝ)) * (1 - 3 * d) :=
    mul_lt_mul_of_pos_right
      oneOverFiftySixThousandFiveHundred_lt_exp_neg_oneHundredSeventyFiveSixteenths hfactor
  have hlinear : 1 - 3 * d ≤ Real.exp (-(3 * d)) := Real.one_sub_le_exp_neg (3 * d)
  calc
    (1 / 56500 : ℝ) * (1 - 3 * (A - 175 / 48)) =
        (1 / 56500 : ℝ) * (1 - 3 * d) := by rfl
    _ < Real.exp (-(175 / 16 : ℝ)) * (1 - 3 * d) := hfirst
    _ ≤ Real.exp (-(175 / 16 : ℝ)) * Real.exp (-(3 * d)) := by gcongr
    _ = Real.exp (-3 * A) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring

/-- Cleared exact-ray certificate for the continued affine fourth floor. -/
theorem exactFourth175Over48AffineFloor_lt_atomEnvelope
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 48) :
    (1000 / 989 : ℝ) * (72 - 192 * d) <
      16 * (399 / 400 : ℝ) *
        ((1 / 56500 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial d := by
  have hB : 0 < 103 / 48 + d := by linarith
  have hmul : (103 / 48 + d) ^ (5 : ℕ) *
      ((1000 / 989 : ℝ) * (72 - 192 * d)) <
    (103 / 48 + d) ^ (5 : ℕ) *
      (16 * (399 / 400 : ℝ) *
        ((1 / 56500 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial d) := by
    dsimp [thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial,
      thetaCuspLikelihoodFourthExactDominantPolynomial, thetaLikelihoodFourthScore]
    field_simp [hB.ne']
    ring_nf
    rw [← sub_pos]
    ring_nf
    have hd2 : d ^ (2 : ℕ) ≤ (1 / 48 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hd hdhi 2
    have hd3 : d ^ (3 : ℕ) ≤ (1 / 48 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hd hdhi 3
    have hd4 : d ^ (4 : ℕ) ≤ (1 / 48 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hd hdhi 4
    have hd5 : d ^ (5 : ℕ) ≤ (1 / 48 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hd hdhi 5
    have hd6 : d ^ (6 : ℕ) ≤ (1 / 48 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hd hdhi 6
    have hd7 : d ^ (7 : ℕ) ≤ (1 / 48 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hd hdhi 7
    have hd8 : d ^ (8 : ℕ) ≤ (1 / 48 : ℝ) ^ (8 : ℕ) := pow_le_pow_left₀ hd hdhi 8
    have hd9 : d ^ (9 : ℕ) ≤ (1 / 48 : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ hd hdhi 9
    have hd10 : d ^ (10 : ℕ) ≤ (1 / 48 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ hd hdhi 10
    have hd11 : d ^ (11 : ℕ) ≤ (1 / 48 : ℝ) ^ (11 : ℕ) := pow_le_pow_left₀ hd hdhi 11
    have hd12 : d ^ (12 : ℕ) ≤ (1 / 48 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ hd hdhi 12
    have hd13 : 0 ≤ d ^ (13 : ℕ) := by positivity
    norm_num at hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 ⊢
    nlinarith
  nlinarith [pow_pos hB 5]

/-- The exact dominant atom-ray score proves the continued ordinary fourth floor. -/
theorem oneThousandOverNineHundredEightyNine_mul_fourth175Over48AffineFloor_lt_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (175 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 11 / 3) :
    (1000 / 989 : ℝ) *
        (772 - 192 * thetaCuspSingleAtomReflectionScale 1 x) <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let d := A - 175 / 48
  let atomFloor := (1 / 56500 : ℝ) * (1 - 3 * d) *
    thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial d
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd : 0 ≤ d := by dsimp only [d, A] at hAlo ⊢; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d, A] at hAhi ⊢; linarith
  have hPolyPos : 0 < thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial d := by
    have hcert := exactFourth175Over48AffineFloor_lt_atomEnvelope hd hdhi
    have hlinear : 0 < 1 - 3 * d := by linarith
    have hprofile : 0 < 72 - 192 * d := by linarith
    have hleft : 0 < (1000 / 989 : ℝ) * (72 - 192 * d) := by
      positivity
    have hprod : 0 <
        (16 * (399 / 400 : ℝ) * ((1 / 56500 : ℝ) * (1 - 3 * d))) *
          thetaCuspLikelihoodFourthScale175Over48ExactDominantPolynomial d := by
      nlinarith
    have hfactor : 0 <
        16 * (399 / 400 : ℝ) * ((1 / 56500 : ℝ) * (1 - 3 * d)) := by
      positivity
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hfactor.le hneg.1).elim
  have hExp := thetaCuspLikelihoodFourthScale175Over48_expAffine_lt_exp_neg_three_mul
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hExp' : (1 / 56500 : ℝ) * (1 - 3 * (A - 175 / 48)) <
      Real.exp (-(3 * A)) := by
    simpa only [A, neg_mul] using hExp
  have hAtomEq := integral_thetaLikelihoodFourthScore_dominantAtom_eq_scale175Over48_exact
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
      have hAt : (175 / 16 : ℝ) ≤ A * t := by
        have hA0 : 0 ≤ A := by dsimp only [A] at hAlo ⊢; linarith
        nlinarith [mul_le_mul hAlo ht (by norm_num : (0 : ℝ) ≤ 3) hA0]
      have hscore :=
        oneHalf_mul_pow_four_le_fourthScore_of_oneHundredSeventyFiveSixteenths_le
          hAt
      have hscore0 : 0 ≤ thetaLikelihoodFourthScore (A * t) := by
        exact (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * (A * t) ^ (4 : ℕ)).trans hscore
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
  have hpoly := exactFourth175Over48AffineFloor_lt_atomEnvelope hd hdhi
  have hprofile : 772 - 192 * A = 72 - 192 * d := by dsimp only [d]; ring
  rw [show thetaCuspSingleAtomReflectionScale 1 x = A by rfl, hprofile]
  exact hpoly.trans (by simpa only [atomFloor, mul_assoc] using hNorm)

/-- Logarithmic fourth-jet floor on `11/3 ≤ A ≤ 59/16`. -/
theorem fourth175Over48AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (175 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 11 / 3) :
    772 - 192 * thetaCuspSingleAtomReflectionScale 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord :=
    oneThousandOverNineHundredEightyNine_mul_fourth175Over48AffineFloor_lt_ordinaryJetFour
      hx hAlo hAhi
  have hretain :=
    nineHundredEightyNineThousandths_mul_ordinaryJetFour_lt_logJetFour_of_175Over48_le hx hAlo
  calc
    772 - 192 * thetaCuspSingleAtomReflectionScale 1 x =
        (989 / 1000 : ℝ) * ((1000 / 989 : ℝ) *
          (772 - 192 * thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ < (989 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

/-- Weight-coordinate form of the exact scale-`11/3` fourth producer. -/
theorem fourth175Over48AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (175 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 11 / 3) :
    484 - 192 * thetaCuspBornWittenWeight 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have h := fourth175Over48AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    hx hAlo hAhi
  convert h using 1
  dsimp [thetaCuspSingleAtomReflectionScale]
  rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
  norm_num
  rw [show 2 * x = x + x by ring, Real.exp_add]
  ring

end
end RHTower
