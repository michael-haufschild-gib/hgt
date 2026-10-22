import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthScaleFifteenFourthsBound

/-!
# Scale-fifteen-fourths affine upper bound for the sixth theta likelihood jet

The scalar scale-`15/4` estimate is sharpened across `15/4 ≤ A ≤ 23/6` by retaining the exact
live ratios `A/B` and `1/B` in the first atom-ray.  With `d = A - 15/4`, the dominant mass is
bounded by `228 - 324d`, the complete mass by `239 - 324d`, and the logarithmic sixth jet by
`(1656/25) * (239 - 324d)`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact rational score factor after extracting `exp (-3A)` from the first atom-ray. -/
def thetaCuspLikelihoodSixthAffineDominantPolynomial (d : ℝ) : ℝ :=
  16 * thetaLikelihoodSixthScoreShift (9 / 4 + 3 * d) +
    18 * (1 / (9 / 4 + d)) *
      thetaLikelihoodSixthScoreRayTransformPolynomial
        ((15 / 4 + d) / (9 / 4 + d)) (9 / 4 + 3 * d)

/-- Cleared exact certificate for the affine dominant-mass budget on `0 ≤ d ≤ 1/12`. -/
theorem thetaCuspLikelihoodSixthAffineDominantPolynomial_lt
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 12) :
    (1 / 76000 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) *
        thetaCuspLikelihoodSixthAffineDominantPolynomial d <
      228 - 324 * d := by
  have hB : 0 < 9 / 4 + d := by linarith
  let y := 1 / 12 - d
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 12 := by dsimp only [y]; linarith
  have hmul : (9 / 4 + d) ^ (7 : ℕ) *
      ((1 / 76000 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) *
          thetaCuspLikelihoodSixthAffineDominantPolynomial d) <
    (9 / 4 + d) ^ (7 : ℕ) * (228 - 324 * d) := by
    dsimp [thetaCuspLikelihoodSixthAffineDominantPolynomial,
      thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    field_simp [hB.ne']
    ring_nf
    rw [show d = 1 / 12 - y by dsimp only [y]; ring]
    ring_nf
    rw [← sub_pos]
    ring_nf
    have hy2 : y ^ (2 : ℕ) ≤ (1 / 12 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hy hyhi 2
    have hy4 : y ^ (4 : ℕ) ≤ (1 / 12 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hy hyhi 4
    have hy6 : y ^ (6 : ℕ) ≤ (1 / 12 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hy hyhi 6
    have hy8 : y ^ (8 : ℕ) ≤ (1 / 12 : ℝ) ^ (8 : ℕ) := pow_le_pow_left₀ hy hyhi 8
    have hy10 : y ^ (10 : ℕ) ≤ (1 / 12 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ hy hyhi 10
    have hy12 : y ^ (12 : ℕ) ≤ (1 / 12 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ hy hyhi 12
    have hy14 : y ^ (14 : ℕ) ≤ (1 / 12 : ℝ) ^ (14 : ℕ) := pow_le_pow_left₀ hy hyhi 14
    have hpositive : 0 ≤
        y ^ (3 : ℕ) * (855784921033986277376 / 81 : ℝ) +
          y ^ (5 : ℕ) * (95442726427912044544 / 3 : ℝ) +
          y ^ (7 : ℕ) * 21276860458090889216 +
          y ^ (9 : ℕ) * 4205535108494524416 +
          y ^ (11 : ℕ) * 254644542253301760 +
          y ^ (13 : ℕ) * 3950969943490560 +
          y ^ (15 : ℕ) * 7044820107264 := by
      positivity
    norm_num at hyhi hy2 hy4 hy6 hy8 hy10 hy12 hy14 ⊢
    nlinarith
  nlinarith [pow_pos hB 7]

/-- The exact dominant first atom-ray mass obeys the affine budget `228 - 324d`. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_affine_of_scale_mem
    (A : ℝ) {B : ℝ} (hAlo : (15 / 4 : ℝ) ≤ A) (hAhi : A ≤ 23 / 6)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B <
      228 - 324 * (A - 15 / 4) := by
  have hB : 0 < B := by rw [hBA]; linarith
  let d := A - 15 / 4
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 12 := by dsimp only [d]; linarith
  have hAeq : A = 15 / 4 + d := by dsimp only [d]; ring
  have hBeq : B = 9 / 4 + d := by rw [hBA, hAeq]; ring
  have hy : 3 * A - 9 = 9 / 4 + 3 * d := by rw [hAeq]; ring
  have hextract :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) = Real.exp (-3 * A) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  have hmassEq : thetaCuspLikelihoodDominantAtomSixthScoreMass A B =
      Real.exp (-3 * A) * thetaCuspLikelihoodSixthAffineDominantPolynomial d := by
    rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB,
      thetaLikelihoodSixthScore_eq_shiftNine, hy]
    rw [show Real.exp (-(3 * B)) / B =
        (Real.exp (-(3 * B)) * (1 / B)) by ring]
    rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScoreShift (9 / 4 + 3 * d) * Real.exp (-(3 * B))) +
        18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (1 / B) *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (9 / 4 + 3 * d)) =
        (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B))) *
          (16 * thetaLikelihoodSixthScoreShift (9 / 4 + 3 * d) +
            18 * (1 / B) *
              thetaLikelihoodSixthScoreRayTransformPolynomial
                (A / B) (9 / 4 + 3 * d)) by ring]
    rw [hextract, hAeq, hBeq]
    rfl
  have hexpd : Real.exp (-(3 * d)) ≤ 1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2 :=
    exp_neg_le_quadratic (by positivity)
  have hExp : Real.exp (-3 * A) <
      (1 / 76000 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) := by
    calc
      Real.exp (-3 * A) =
          Real.exp (-(45 / 4 : ℝ)) * Real.exp (-(3 * d)) := by
        rw [← Real.exp_add, hAeq]
        congr 1
        ring
      _ < (1 / 76000 : ℝ) * Real.exp (-(3 * d)) := by
        gcongr
        exact exp_neg_fortyFiveFourths_lt_oneSeventySixThousand
      _ ≤ (1 / 76000 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) := by gcongr
  have hpolypos : 0 < thetaCuspLikelihoodSixthAffineDominantPolynomial d := by
    have hBd : 0 < 9 / 4 + d := by linarith
    dsimp [thetaCuspLikelihoodSixthAffineDominantPolynomial,
      thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    positivity
  have hpoly := thetaCuspLikelihoodSixthAffineDominantPolynomial_lt hd hdhi
  rw [hmassEq]
  exact (mul_lt_mul_of_pos_right hExp hpolypos).trans hpoly

/-- Dominant plus stable sixth-score mass is below `239 - 324(A - 15/4)`. -/
theorem integral_thetaLikelihoodSixthScore_lt_affine_of_scale_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 23 / 6) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore
            (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) <
      239 - 324 * (thetaCuspSingleAtomReflectionScale 1 x - 15 / 4) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 15 / 4)).le.trans hAlo
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd := thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_affine_of_scale_mem
    A (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hs := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_le hApi hBA
  have hpi2 : Real.pi ^ (2 : ℕ) < (10 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpi6 : Real.pi ^ (6 : ℕ) < (1000 : ℝ) := by
    have h := pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi) (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Real.pi ^ (6 : ℕ) = (Real.pi ^ (2 : ℕ)) ^ (3 : ℕ) := by ring
      _ < (10 : ℝ) ^ (3 : ℕ) := h
      _ = 1000 := by norm_num
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [A, B] at hd hs ⊢
  nlinarith

/-- Affine logarithmic sixth-jet ceiling throughout the scale-`15/4` compact chamber. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_affine_of_scale_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 23 / 6) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1656 / 25 : ℝ) *
        (239 - 324 * (thetaCuspSingleAtomReflectionScale 1 x - 15 / 4)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let massBudget := 239 - 324 * (A - 15 / 4)
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    have hzero := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
    change 1 ≤ thetaCuspLikelihoodPartition B
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    linarith
  have hbudget : 0 < massBudget := by
    dsimp only [massBudget, A]
    linarith
  have hscore :
      (∫ t : ℝ,
          thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) < massBudget := by
    simpa only [A, B, massBudget] using
      integral_thetaLikelihoodSixthScore_lt_affine_of_scale_mem hx hAlo hAhi
  have hordinary : thetaCuspLikelihoodSourceOrdinaryJetSix x < 64 * massBudget := by
    have hordinaryPos := thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx]
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx] at hordinaryPos
    have hcoeff : 0 < 64 / P := div_pos (by norm_num) hP
    have hcoeffUpper : 64 / P ≤ 64 := by
      apply (div_le_iff₀ hP).2
      nlinarith
    have hmass0 : 0 < (∫ t : ℝ,
        thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
      dsimp only [A, B] at hordinaryPos ⊢
      nlinarith
    dsimp only [A, B] at hscore ⊢
    nlinarith [mul_lt_mul_of_pos_left hscore hcoeff,
      mul_le_mul_of_nonneg_right hcoeffUpper hmass0.le]
  have hlog :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary hx
  dsimp only [massBudget, A] at hordinary ⊢
  nlinarith

/-- Weight-coordinate form of the affine sixth-jet ceiling. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_affine_weight_of_scale_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 23 / 6) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1656 / 25 : ℝ) * (968 - 324 * thetaCuspBornWittenWeight 1 x) := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_affine_of_scale_mem
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1 <;> ring

end
end RHTower
