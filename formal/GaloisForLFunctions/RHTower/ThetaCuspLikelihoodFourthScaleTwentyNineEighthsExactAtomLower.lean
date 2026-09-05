import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthDominantAtomExact
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingTwentyNineEighths
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderQuadrature

/-!
# Exact scale-29/8 fourth atom-ray producer

The scale-free dominant-atom identity, a fourth-power `exp(1/32)` certificate, and the
`1694/1695` partition normalization continue the global affine fourth floor across
`29/8 ≤ A ≤ 175/48`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Chamber specialization of the exact dominant fourth-score factor. -/
def thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial (d : ℝ) : ℝ :=
  thetaCuspLikelihoodFourthExactDominantPolynomial (29 / 8 + d) (17 / 8 + d)

/-- Rational lower enclosure for `exp (-87/8)`. -/
theorem oneOverFiftyTwoThousandEightHundredFifty_lt_exp_neg_eightySevenEighths :
    (1 / 52850 : ℝ) < Real.exp (-(87 / 8 : ℝ)) := by
  have hpow11 : Real.exp 1 ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le
      (by norm_num : (11 : ℕ) ≠ 0)
  have h11 : Real.exp 11 < (59875 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hneg11 : (1 / 59875 : ℝ) < Real.exp (-11) := by
    have hprod : Real.exp (-11) * Real.exp 11 = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (-11)]
  have hsmall := thetaCuspThirtySecondExpTaylorLower_pow_le_exp 4
  have hfactor :
      thetaCuspThirtySecondExpTaylorLower ^ 4 ≤ Real.exp (1 / 8 : ℝ) := by
    convert hsmall using 1 <;> norm_num
  have hproduct : Real.exp (-(87 / 8 : ℝ)) =
      Real.exp (-11) * Real.exp (1 / 8) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [hproduct]
  have hpowpos : 0 < thetaCuspThirtySecondExpTaylorLower ^ 4 := by
    norm_num [thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hlower : (1 / 59875 : ℝ) * thetaCuspThirtySecondExpTaylorLower ^ 4 <
      Real.exp (-11) * Real.exp (1 / 8) :=
    (mul_lt_mul_of_pos_right hneg11 hpowpos).trans_le
      (mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le)
  exact (show (1 / 52850 : ℝ) <
      (1 / 59875 : ℝ) * thetaCuspThirtySecondExpTaylorLower ^ 4 by
        norm_num [thetaCuspThirtySecondExpTaylorLower,
          thetaCuspExpTwoTaylorEightPolynomial]).trans hlower

/-- Live affine lower enclosure for `exp (-3A)` on the chamber. -/
theorem thetaCuspLikelihoodFourthScale29Over8_expAffine_lt_exp_neg_three_mul
    {A : ℝ} (hAlo : (29 / 8 : ℝ) ≤ A) (hAhi : A ≤ 175 / 48) :
    (1 / 52850 : ℝ) * (1 - 3 * (A - 29 / 8)) < Real.exp (-3 * A) := by
  let d := A - 29 / 8
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d]; linarith
  have hfactor : 0 < 1 - 3 * d := by linarith
  have hfirst : (1 / 52850 : ℝ) * (1 - 3 * d) <
      Real.exp (-(87 / 8 : ℝ)) * (1 - 3 * d) :=
    mul_lt_mul_of_pos_right
      oneOverFiftyTwoThousandEightHundredFifty_lt_exp_neg_eightySevenEighths hfactor
  have hlinear : 1 - 3 * d ≤ Real.exp (-(3 * d)) := Real.one_sub_le_exp_neg (3 * d)
  calc
    (1 / 52850 : ℝ) * (1 - 3 * (A - 29 / 8)) =
        (1 / 52850 : ℝ) * (1 - 3 * d) := by rfl
    _ < Real.exp (-(87 / 8 : ℝ)) * (1 - 3 * d) := hfirst
    _ ≤ Real.exp (-(87 / 8 : ℝ)) * Real.exp (-(3 * d)) := by gcongr
    _ = Real.exp (-3 * A) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring

/-- Cleared exact-ray certificate for the continued affine fourth floor. -/
theorem exactFourth29Over8AffineFloor_lt_atomEnvelope
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 48) :
    (10000 / 9896 : ℝ) * (153 / 2 - 192 * d) <
      16 * (1694 / 1695 : ℝ) *
        ((1 / 52850 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial d := by
  have hB : 0 < 17 / 8 + d := by linarith
  have hmul : (17 / 8 + d) ^ 5 *
      ((10000 / 9896 : ℝ) * (153 / 2 - 192 * d)) <
    (17 / 8 + d) ^ 5 *
      (16 * (1694 / 1695 : ℝ) *
        ((1 / 52850 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial d) := by
    dsimp [thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial,
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

/-- Exact dominant atom proves the continued ordinary fourth floor. -/
theorem tenThousandOverNineThousandEightHundredNinetySix_mul_fourth29Over8AffineFloor_lt_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (29 / 8 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    (10000 / 9896 : ℝ) *
        (1545 / 2 - 192 * thetaCuspSingleAtomReflectionScale 1 x) <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let d := A - 29 / 8
  let atomFloor := (1 / 52850 : ℝ) * (1 - 3 * d) *
    thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial d
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd : 0 ≤ d := by dsimp only [d, A] at hAlo ⊢; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d, A] at hAhi ⊢; linarith
  have hPolyPos : 0 < thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial d := by
    have hcert := exactFourth29Over8AffineFloor_lt_atomEnvelope hd hdhi
    have hlinear : 0 < 1 - 3 * d := by linarith
    have hprofile : 0 < 153 / 2 - 192 * d := by linarith
    have hleft : 0 < (10000 / 9896 : ℝ) * (153 / 2 - 192 * d) := by positivity
    have hfactor : 0 <
        16 * (1694 / 1695 : ℝ) * ((1 / 52850 : ℝ) * (1 - 3 * d)) := by
      positivity
    have hprod : 0 <
        (16 * (1694 / 1695 : ℝ) * ((1 / 52850 : ℝ) * (1 - 3 * d))) *
          thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial d :=
      hleft.trans hcert
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hfactor.le hneg.1).elim
  have hExp := thetaCuspLikelihoodFourthScale29Over8_expAffine_lt_exp_neg_three_mul
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hExp' : (1 / 52850 : ℝ) * (1 - 3 * (A - 29 / 8)) <
      Real.exp (-(3 * A)) := by
    simpa only [A, neg_mul] using hExp
  have hAShift : (29 / 8 : ℝ) + d = A := by dsimp only [d]; ring
  have hBShift : (17 / 8 : ℝ) + d = B := by
    dsimp only [d]
    rw [hBA]
    ring
  have hPolyPosAB : 0 < thetaCuspLikelihoodFourthExactDominantPolynomial A B := by
    simpa only [thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial,
      hAShift, hBShift] using hPolyPos
  have hPolySpecialEq :
      thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial (A - 29 / 8) =
        thetaCuspLikelihoodFourthExactDominantPolynomial A B := by
    dsimp only [thetaCuspLikelihoodFourthScale29Over8ExactDominantPolynomial]
    rw [show (29 / 8 : ℝ) + (A - 29 / 8) = A by ring]
    rw [show (17 / 8 : ℝ) + (A - 29 / 8) = B by rw [hBA]; ring]
  have hAtomEq := integral_thetaLikelihoodFourthScore_dominantAtom_eq_exact hB hBA
  have hAtom : atomFloor <
      ∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
    rw [hAtomEq]
    dsimp only [atomFloor]
    rw [show d = A - 29 / 8 by rfl]
    rw [hPolySpecialEq]
    exact mul_lt_mul_of_pos_right hExp' hPolyPosAB
  have hMeasure : thetaCuspAtomLikelihoodSpectralMeasure 2 ≤
      thetaCuspHigherLikelihoodSpectralMeasure := by
    rw [thetaCuspHigherLikelihoodSpectralMeasure]
    simpa only [Nat.zero_add] using
      Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0
  have hInt := integrable_thetaLikelihoodFourthScore_mul_exp_higher_general A hB
  have hMono :
      (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspAtomLikelihoodSpectralMeasure 2) ≤
        ∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure := by
    apply integral_mono_measure hMeasure
    · filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
      have hA0 : 0 ≤ A := by dsimp only [A] at hAlo ⊢; linarith
      have hAt : (47 / 5 : ℝ) ≤ A * t := by
        nlinarith [mul_le_mul hAlo ht (by norm_num : (0 : ℝ) ≤ 3) hA0]
      have hscore := two_fifths_mul_pow_four_le_thetaLikelihoodFourthScore hAt
      have hbase : 0 ≤ (2 / 5 : ℝ) * (A * t) ^ 4 := by positivity
      exact mul_nonneg (hbase.trans hscore) (Real.exp_pos (-(B * t))).le
    · exact hInt
  have hTotal := hAtom.trans_le hMono
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  let p := thetaCuspLikelihoodTailProbability B
  have hpSmall : 1695 * p < 1 := by
    simpa only [B, p] using
      oneThousandSixHundredNinetyFive_mul_thetaCuspLikelihoodTailProbability_lt_one_of_29Over8_le
        hx hAlo
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
  have hPinv : (1694 / 1695 : ℝ) < 1 / P := by
    rw [hpEq] at hpSmall
    linarith
  have hfloor : 0 < atomFloor := by
    have hlinear : 0 < 1 - 3 * d := by linarith
    dsimp only [atomFloor]
    positivity
  have hNorm : 16 * (1694 / 1695 : ℝ) * atomFloor <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
    have hIntegralEq := integral_thetaLikelihoodFourthScore_mul_exp_higher_eq_general A hB
    calc
      16 * (1694 / 1695 : ℝ) * atomFloor < 16 * ((1 / P) * atomFloor) := by
        have := mul_lt_mul_of_pos_right hPinv hfloor
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
  have hpoly := exactFourth29Over8AffineFloor_lt_atomEnvelope hd hdhi
  have hprofile : 1545 / 2 - 192 * A = 153 / 2 - 192 * d := by
    dsimp only [d]
    ring
  rw [show thetaCuspSingleAtomReflectionScale 1 x = A by rfl, hprofile]
  exact hpoly.trans (by simpa only [atomFloor, mul_assoc] using hNorm)

/-- Logarithmic fourth-jet floor on `29/8 ≤ A ≤ 175/48`. -/
theorem fourth29Over8AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (29 / 8 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    1545 / 2 - 192 * thetaCuspSingleAtomReflectionScale 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord :=
    tenThousandOverNineThousandEightHundredNinetySix_mul_fourth29Over8AffineFloor_lt_ordinaryJetFour
      hx hAlo hAhi
  have hretain :=
    nineThousandEightHundredNinetySixTenThousandths_mul_ordinaryJetFour_lt_logJetFour_of_29Over8_le
      hx hAlo
  calc
    1545 / 2 - 192 * thetaCuspSingleAtomReflectionScale 1 x =
        (9896 / 10000 : ℝ) * ((10000 / 9896 : ℝ) *
          (1545 / 2 - 192 * thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ < (9896 / 10000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

/-- Weight-coordinate form of the scale-`29/8` fourth producer. -/
theorem fourth29Over8AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (29 / 8 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    969 / 2 - 192 * thetaCuspBornWittenWeight 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have h := fourth29Over8AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    hx hAlo hAhi
  convert h using 1
  dsimp [thetaCuspSingleAtomReflectionScale]
  rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
  norm_num
  rw [show 2 * x = x + x by ring, Real.exp_add]
  ring

end

end RHTower
