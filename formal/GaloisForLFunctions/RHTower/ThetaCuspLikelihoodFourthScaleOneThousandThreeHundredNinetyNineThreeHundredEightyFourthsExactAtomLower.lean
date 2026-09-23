import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthDominantAtomExact
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingOneThousandThreeHundredNinetyNineThreeHundredEightyFourths

/-!
# Exact scale-1399/384 fourth atom-ray producer

The scale-free dominant-atom identity, live exponential lower enclosure, and improved
`1595/1596` partition normalization extend the global affine fourth floor across the chamber of
width `1/384`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Chamber specialization of the exact dominant fourth-score factor. -/
def thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial (d : ℝ) : ℝ :=
  thetaCuspLikelihoodFourthExactDominantPolynomial
    (1399 / 384 + d) (823 / 384 + d)

/-- Rational lower enclosure for `exp (-1399/128)`. -/
theorem oneOverFiftySixThousand_lt_exp_neg_oneThousandThreeHundredNinetyNineOneHundredTwentyEighths :
    (1 / 56000 : ℝ) < Real.exp (-(1399 / 128 : ℝ)) := by
  have hpow11 : Real.exp 1 ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h11 : Real.exp 11 < (59875 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hsmall : Real.exp (-(9 / 128 : ℝ)) ≤ 128 / 137 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 128) 2
    have hpos := Real.exp_pos (-(9 / 128 : ℝ))
    have hprod : Real.exp (-(9 / 128 : ℝ)) * Real.exp (9 / 128 : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    nlinarith
  have h1399 : Real.exp (1399 / 128 : ℝ) < 56000 := by
    rw [show (1399 / 128 : ℝ) = 11 + (-(9 / 128 : ℝ)) by norm_num,
      Real.exp_add]
    nlinarith [Real.exp_pos 11]
  have hprod : Real.exp (-(1399 / 128 : ℝ)) * Real.exp (1399 / 128 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(1399 / 128 : ℝ))]

/-- Live affine lower enclosure for `exp (-3A)` on the chamber. -/
theorem thetaCuspLikelihoodFourthScale1399Over384_expAffine_lt_exp_neg_three_mul
    {A : ℝ} (hAlo : (1399 / 384 : ℝ) ≤ A) (hAhi : A ≤ 175 / 48) :
    (1 / 56000 : ℝ) * (1 - 3 * (A - 1399 / 384)) < Real.exp (-3 * A) := by
  let d := A - 1399 / 384
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 384 := by dsimp only [d]; linarith
  have hfactor : 0 < 1 - 3 * d := by linarith
  have hfirst : (1 / 56000 : ℝ) * (1 - 3 * d) <
      Real.exp (-(1399 / 128 : ℝ)) * (1 - 3 * d) :=
    mul_lt_mul_of_pos_right
      oneOverFiftySixThousand_lt_exp_neg_oneThousandThreeHundredNinetyNineOneHundredTwentyEighths
      hfactor
  have hlinear : 1 - 3 * d ≤ Real.exp (-(3 * d)) := Real.one_sub_le_exp_neg (3 * d)
  calc
    (1 / 56000 : ℝ) * (1 - 3 * (A - 1399 / 384)) =
        (1 / 56000 : ℝ) * (1 - 3 * d) := by rfl
    _ < Real.exp (-(1399 / 128 : ℝ)) * (1 - 3 * d) := hfirst
    _ ≤ Real.exp (-(1399 / 128 : ℝ)) * Real.exp (-(3 * d)) := by gcongr
    _ = Real.exp (-3 * A) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring

/-- Cleared exact-ray certificate for the continued affine fourth floor. -/
theorem exactFourth1399Over384AffineFloor_lt_atomEnvelope
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 384) :
    (1000 / 989 : ℝ) * (145 / 2 - 192 * d) <
      16 * (1595 / 1596 : ℝ) *
        ((1 / 56000 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial d := by
  have hB : 0 < 823 / 384 + d := by linarith
  have hmul : (823 / 384 + d) ^ (5 : ℕ) *
      ((1000 / 989 : ℝ) * (145 / 2 - 192 * d)) <
    (823 / 384 + d) ^ (5 : ℕ) *
      (16 * (1595 / 1596 : ℝ) *
        ((1 / 56000 : ℝ) * (1 - 3 * d)) *
        thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial d) := by
    dsimp [thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial,
      thetaCuspLikelihoodFourthExactDominantPolynomial, thetaLikelihoodFourthScore]
    field_simp [hB.ne']
    ring_nf
    rw [← sub_pos]
    ring_nf
    have hd2 : d ^ (2 : ℕ) ≤ (1 / 384 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hd hdhi 2
    have hd3 : d ^ (3 : ℕ) ≤ (1 / 384 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hd hdhi 3
    have hd4 : d ^ (4 : ℕ) ≤ (1 / 384 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hd hdhi 4
    have hd5 : d ^ (5 : ℕ) ≤ (1 / 384 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hd hdhi 5
    have hd6 : d ^ (6 : ℕ) ≤ (1 / 384 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hd hdhi 6
    have hd7 : d ^ (7 : ℕ) ≤ (1 / 384 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hd hdhi 7
    have hd8 : d ^ (8 : ℕ) ≤ (1 / 384 : ℝ) ^ (8 : ℕ) := pow_le_pow_left₀ hd hdhi 8
    have hd9 : d ^ (9 : ℕ) ≤ (1 / 384 : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ hd hdhi 9
    have hd10 : d ^ (10 : ℕ) ≤ (1 / 384 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ hd hdhi 10
    have hd11 : d ^ (11 : ℕ) ≤ (1 / 384 : ℝ) ^ (11 : ℕ) := pow_le_pow_left₀ hd hdhi 11
    have hd12 : d ^ (12 : ℕ) ≤ (1 / 384 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ hd hdhi 12
    have hd13 : 0 ≤ d ^ (13 : ℕ) := by positivity
    norm_num at hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 ⊢
    nlinarith
  nlinarith [pow_pos hB 5]

/-- Exact dominant atom proves the continued ordinary fourth floor. -/
theorem oneThousandOverNineHundredEightyNine_mul_fourth1399Over384AffineFloor_lt_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (1399 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    (1000 / 989 : ℝ) *
        (772 - 192 * thetaCuspSingleAtomReflectionScale 1 x) <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let d := A - 1399 / 384
  let atomFloor := (1 / 56000 : ℝ) * (1 - 3 * d) *
    thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial d
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd : 0 ≤ d := by dsimp only [d, A] at hAlo ⊢; linarith
  have hdhi : d ≤ 1 / 384 := by dsimp only [d, A] at hAhi ⊢; linarith
  have hPolyPos : 0 < thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial d := by
    have hcert := exactFourth1399Over384AffineFloor_lt_atomEnvelope hd hdhi
    have hlinear : 0 < 1 - 3 * d := by linarith
    have hprofile : 0 < 145 / 2 - 192 * d := by linarith
    have hleft : 0 < (1000 / 989 : ℝ) * (145 / 2 - 192 * d) := by
      positivity
    have hfactor : 0 <
        16 * (1595 / 1596 : ℝ) * ((1 / 56000 : ℝ) * (1 - 3 * d)) := by
      positivity
    have hprod : 0 <
        (16 * (1595 / 1596 : ℝ) * ((1 / 56000 : ℝ) * (1 - 3 * d))) *
          thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial d :=
      hleft.trans hcert
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hfactor.le hneg.1).elim
  have hExp := thetaCuspLikelihoodFourthScale1399Over384_expAffine_lt_exp_neg_three_mul
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hExp' : (1 / 56000 : ℝ) * (1 - 3 * (A - 1399 / 384)) <
      Real.exp (-(3 * A)) := by
    simpa only [A, neg_mul] using hExp
  have hAShift : (1399 / 384 : ℝ) + d = A := by dsimp only [d]; ring
  have hBShift : (823 / 384 : ℝ) + d = B := by
    dsimp only [d]
    rw [hBA]
    ring
  have hPolyPosAB : 0 < thetaCuspLikelihoodFourthExactDominantPolynomial A B := by
    simpa only [thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial,
      hAShift, hBShift] using hPolyPos
  have hPolySpecialEq :
      thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial
          (A - 1399 / 384) =
        thetaCuspLikelihoodFourthExactDominantPolynomial A B := by
    dsimp only [thetaCuspLikelihoodFourthScale1399Over384ExactDominantPolynomial]
    rw [show (1399 / 384 : ℝ) + (A - 1399 / 384) = A by ring]
    rw [show (823 / 384 : ℝ) + (A - 1399 / 384) = B by rw [hBA]; ring]
  have hAtomEq := integral_thetaLikelihoodFourthScore_dominantAtom_eq_exact hB hBA
  have hAtom : atomFloor <
      ∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
    rw [hAtomEq]
    dsimp only [atomFloor]
    rw [show d = A - 1399 / 384 by rfl]
    rw [hPolySpecialEq]
    have hmul := mul_lt_mul_of_pos_right hExp' hPolyPosAB
    exact hmul
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
      have hbase : 0 ≤ (2 / 5 : ℝ) * (A * t) ^ (4 : ℕ) := by positivity
      exact mul_nonneg (hbase.trans hscore) (Real.exp_pos (-(B * t))).le
    · exact hInt
  have hTotal := hAtom.trans_le hMono
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  let p := thetaCuspLikelihoodTailProbability B
  have hpSmall : 1596 * p < 1 := by
    simpa only [B, p] using
      oneThousandFiveHundredNinetySix_mul_thetaCuspLikelihoodTailProbability_lt_one_of_1399Over384_le
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
  have hPinv : (1595 / 1596 : ℝ) < 1 / P := by
    rw [hpEq] at hpSmall
    linarith
  have hfloor : 0 < atomFloor := by
    have hlinear : 0 < 1 - 3 * d := by linarith
    dsimp only [atomFloor]
    positivity
  have hNorm : 16 * (1595 / 1596 : ℝ) * atomFloor <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
    have hIntegralEq := integral_thetaLikelihoodFourthScore_mul_exp_higher_eq_general A hB
    calc
      16 * (1595 / 1596 : ℝ) * atomFloor < 16 * ((1 / P) * atomFloor) := by
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
  have hpoly := exactFourth1399Over384AffineFloor_lt_atomEnvelope hd hdhi
  have hprofile : 772 - 192 * A = 145 / 2 - 192 * d := by dsimp only [d]; ring
  rw [show thetaCuspSingleAtomReflectionScale 1 x = A by rfl, hprofile]
  exact hpoly.trans (by simpa only [atomFloor, mul_assoc] using hNorm)

/-- Logarithmic fourth-jet floor on the scale-`1399/384` chamber. -/
theorem fourth1399Over384AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (1399 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    772 - 192 * thetaCuspSingleAtomReflectionScale 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord :=
    oneThousandOverNineHundredEightyNine_mul_fourth1399Over384AffineFloor_lt_ordinaryJetFour
      hx hAlo hAhi
  have hretain :=
    nineHundredEightyNineThousandths_mul_ordinaryJetFour_lt_logJetFour_of_1399Over384_le
      hx hAlo
  calc
    772 - 192 * thetaCuspSingleAtomReflectionScale 1 x =
        (989 / 1000 : ℝ) * ((1000 / 989 : ℝ) *
          (772 - 192 * thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ < (989 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

/-- Weight-coordinate form of the scale-`1399/384` fourth producer. -/
theorem fourth1399Over384AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (1399 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    484 - 192 * thetaCuspBornWittenWeight 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have h := fourth1399Over384AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    hx hAlo hAhi
  convert h using 1
  dsimp [thetaCuspSingleAtomReflectionScale]
  rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
  norm_num
  rw [show 2 * x = x + x by ring, Real.exp_add]
  ring

end

end RHTower
