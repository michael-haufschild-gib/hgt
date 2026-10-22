import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthSixthSpectralDomination
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthAtomPairTrace

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Above the compact score edge `23/2`, at least half of the leading fourth monomial survives. -/
theorem oneHalf_mul_pow_four_le_thetaLikelihoodFourthScore
    {z : ℝ} (hz : (23 / 2 : ℝ) ≤ z) :
    (1 / 2 : ℝ) * z ^ (4 : ℕ) ≤ thetaLikelihoodFourthScore z := by
  let y := z - 23 / 2
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  rw [show z = 23 / 2 + y by dsimp only [y]; ring]
  dsimp [thetaLikelihoodFourthScore]
  ring_nf
  nlinarith

private theorem integrable_thetaLikelihoodFourthScore_tilted_lower
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodFourthScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) :=
  integrable_thetaLikelihoodFourthScore_tilted A hB

private theorem integral_thetaLikelihoodFourthScore_tilted_eq_lower
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t)
      ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        6 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        7 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 :=
  integral_thetaLikelihoodFourthScore_tilted_eq A hB

/-- On the scale chamber `A ≥ 23/6`, the ordinary fourth score retains half its leading
spectral moment. -/
theorem eight_mul_scale_pow_four_momentFour_le_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (23 / 6 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    8 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 ≤
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hI4 := integrable_thetaLikelihoodFourthScore_tilted_lower A hB
  have hlead : Integrable (fun t : ℝ =>
      (1 / 2 : ℝ) * A ^ (4 : ℕ) * t ^ (4 : ℕ))
      (thetaCuspHigherLikelihoodTiltedMeasure B) :=
    (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul _
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure B,
      (1 / 2 : ℝ) * A ^ (4 : ℕ) * t ^ (4 : ℕ) ≤ thetaLikelihoodFourthScore (A * t) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    have hAt : (23 / 2 : ℝ) ≤ A * t := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ t),
        mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 23 / 6)]
    have h := oneHalf_mul_pow_four_le_thetaLikelihoodFourthScore hAt
    calc
      (1 / 2 : ℝ) * A ^ (4 : ℕ) * t ^ (4 : ℕ) = (1 / 2 : ℝ) * (A * t) ^ (4 : ℕ) := by ring
      _ ≤ thetaLikelihoodFourthScore (A * t) := h
  have hint := integral_mono_ae hlead hI4 hpoint
  rw [integral_const_mul, integral_thetaLikelihoodFourthScore_tilted_eq_lower A hB] at hint
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hcoeff : 0 ≤ 16 / P := div_nonneg (by norm_num) hP.le
  have hscaled := mul_le_mul_of_nonneg_left hint hcoeff
  calc
    8 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 =
      (16 / P) * ((1 / 2 : ℝ) * A ^ (4 : ℕ) *
        thetaCuspHigherLikelihoodSpectralMoment B 4) := by
          dsimp only [A, B]
          unfold thetaCuspLikelihoodNormalizedMoment
          dsimp only [P]
          field_simp [hP.ne']
          ring
    _ ≤ (16 / P) *
        (A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          6 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          7 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
          A * thetaCuspHigherLikelihoodSpectralMoment B 1) := hscaled
    _ = thetaCuspLikelihoodSourceOrdinaryJetFour x := by
      dsimp only [thetaCuspLikelihoodSourceOrdinaryJetFour, A, B]
      unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
      dsimp only [P]
      field_simp [hP.ne']
      ring

/-- Rational lower enclosure for the compact endpoint exponential. -/
theorem oneOverOneHundredTwentyThousand_lt_exp_neg_ninetyThreeEighths :
    (1 / 120000 : ℝ) < Real.exp (-(93 / 8 : ℝ)) := by
  have hpow11 : Real.exp 1 ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h11 : Real.exp 11 < (60000 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hsmall := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 5 / 64 by norm_num) (show (5 / 64 : ℝ) < 1 by norm_num)
  have hpow8 := pow_le_pow_left₀ (Real.exp_pos (5 / 64 : ℝ)).le hsmall 8
  have hfiveEighths : Real.exp (5 / 8 : ℝ) < 2 := by
    rw [show (5 / 8 : ℝ) = (8 : ℕ) * (5 / 64 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact hpow8.trans_lt (by norm_num)
  have hupper : Real.exp (93 / 8 : ℝ) < 120000 := by
    rw [show (93 / 8 : ℝ) = 11 + 5 / 8 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 11, Real.exp_pos (5 / 8 : ℝ)]
  have hprod : Real.exp (-(93 / 8 : ℝ)) * Real.exp (93 / 8 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_lt_mul_of_pos_left hupper (Real.exp_pos (-(93 / 8 : ℝ)))
  rw [hprod] at hmul
  nlinarith

/-- The complete dominant atom-ray fourth moment stays above `11/600` throughout the compact
scale band `23/6 ≤ A ≤ 31/8`. -/
theorem elevenSixHundredths_lt_dominantAtomMomentFour
    {A B : ℝ} (hAlo : (23 / 6 : ℝ) ≤ A) (hAhi : A ≤ (31 / 8 : ℝ))
    (hBA : B = A - 3 / 2) :
    (11 / 600 : ℝ) <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hBupper : B ≤ (19 / 8 : ℝ) := by rw [hBA]; linarith
  have hBthree : B ≤ 3 := by linarith
  have hinv1 : (8 / 19 : ℝ) ≤ 1 / B := by
    have h := one_div_le_one_div_of_le hB hBupper
    norm_num at h ⊢
    exact h
  have hinv2 : (1 / 9 : ℝ) ≤ 1 / B ^ (2 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBthree 2
    have h := one_div_le_one_div_of_le (pow_pos hB 2) hp
    norm_num at h ⊢
    exact h
  have hinv3 : (1 / 27 : ℝ) ≤ 1 / B ^ (3 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBthree 3
    have h := one_div_le_one_div_of_le (pow_pos hB 3) hp
    norm_num at h ⊢
    exact h
  have hinv4 : (1 / 81 : ℝ) ≤ 1 / B ^ (4 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBthree 4
    have h := one_div_le_one_div_of_le (pow_pos hB 4) hp
    norm_num at h ⊢
    exact h
  have hinv5 : (1 / 243 : ℝ) ≤ 1 / B ^ (5 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBthree 5
    have h := one_div_le_one_div_of_le (pow_pos hB 5) hp
    norm_num at h ⊢
    exact h
  let Q := 1296 + 18 *
    (81 / B + 108 / B ^ (2 : ℕ) + 108 / B ^ (3 : ℕ) + 72 / B ^ (4 : ℕ) + 24 / B ^ (5 : ℕ))
  have hQ : (2200 : ℝ) < Q := by
    dsimp only [Q]
    simp only [div_eq_mul_inv] at hinv1 hinv2 hinv3 hinv4 hinv5 ⊢
    nlinarith
  have hexp : (1 / 120000 : ℝ) < Real.exp (-3 * A) := by
    have hmono : Real.exp (-(93 / 8 : ℝ)) ≤ Real.exp (-3 * A) :=
      Real.exp_le_exp.mpr (by linarith)
    exact oneOverOneHundredTwentyThousand_lt_exp_neg_ninetyThreeEighths.trans_le hmono
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
    (n := 2) (by norm_num) 4 hB]
  norm_num [thetaCuspLikelihoodGap, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  have hpref :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(B * 3)) = Real.exp (-3 * A) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  rw [hpref]
  change (11 / 600 : ℝ) < Real.exp (-3 * A) * Q
  calc
    (11 / 600 : ℝ) = (1 / 120000 : ℝ) * 2200 := by norm_num
    _ < Real.exp (-3 * A) * 2200 :=
      mul_lt_mul_of_pos_right hexp (by norm_num)
    _ < Real.exp (-3 * A) * Q :=
      mul_lt_mul_of_pos_left hQ (Real.exp_pos _)

/-- The ordinary fourth likelihood score exceeds `30` on the compact scale band
`23/6 ≤ A ≤ 31/8`. -/
theorem thirty_lt_thetaCuspLikelihoodSourceOrdinaryJetFour_of_scale_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (23 / 6 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (31 / 8 : ℝ)) :
    30 < thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let p := thetaCuspLikelihoodTailProbability B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hAtom : (11 / 600 : ℝ) <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 :=
    elevenSixHundredths_lt_dominantAtomMomentFour
      (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hMeasure : thetaCuspAtomLikelihoodSpectralMeasure 2 ≤
      thetaCuspHigherLikelihoodSpectralMeasure := by
    rw [thetaCuspHigherLikelihoodSpectralMeasure]
    simpa only [Nat.zero_add] using
      Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0
  have hInt := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB
  have hMono :
      (∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-B * t)
          ∂thetaCuspAtomLikelihoodSpectralMeasure 2) ≤
        ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-B * t)
          ∂thetaCuspHigherLikelihoodSpectralMeasure := by
    apply integral_mono_measure hMeasure
    · exact ae_of_all _ fun t => by positivity
    · exact hInt
  have hMoment : (11 / 600 : ℝ) < thetaCuspHigherLikelihoodSpectralMoment B 4 := by
    rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
    have hAtom' : (11 / 600 : ℝ) <
        ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-B * t)
          ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
      simpa only [neg_mul] using hAtom
    exact hAtom'.trans_le hMono
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
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
  have hNorm : (399 / 400 : ℝ) * (11 / 600 : ℝ) <
      thetaCuspLikelihoodNormalizedMoment B 4 := by
    have hfirst := mul_lt_mul_of_pos_right hPinv (by norm_num : (0 : ℝ) < 11 / 600)
    have hsecond := mul_lt_mul_of_pos_left hMoment (by positivity : (0 : ℝ) < 1 / P)
    unfold thetaCuspLikelihoodNormalizedMoment
    calc
      (399 / 400 : ℝ) * (11 / 600 : ℝ) < (1 / P) * (11 / 600 : ℝ) := hfirst
      _ < (1 / P) * thetaCuspHigherLikelihoodSpectralMoment B 4 := hsecond
      _ = thetaCuspHigherLikelihoodSpectralMoment B 4 / P := by ring
  have hbase := eight_mul_scale_pow_four_momentFour_le_ordinaryJetFour hx hAlo
  have hNormX : (399 / 400 : ℝ) * (11 / 600 : ℝ) <
      thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 := by
    simpa only [B] using hNorm
  calc
    (30 : ℝ) < 8 * (23 / 6 : ℝ) ^ (4 : ℕ) *
        ((399 / 400 : ℝ) * (11 / 600 : ℝ)) := by norm_num
    _ ≤ 8 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        ((399 / 400 : ℝ) * (11 / 600 : ℝ)) := by
      gcongr
    _ < 8 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 := by
      gcongr
    _ ≤ thetaCuspLikelihoodSourceOrdinaryJetFour x := hbase

set_option maxHeartbeats 3000000 in
/-- The logarithmic fourth likelihood jet retains more than nineteen twentieths of its
one-particle ordinary score. -/
theorem nineteenTwentieths_mul_ordinaryJetFour_lt_logJetFour
    {x : ℝ} (hx : 0 ≤ x) :
    (19 / 20 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x :=
  nineteenTwentieths_mul_ordinary_lt_thetaCuspLikelihoodSourceLogPartitionJetFour hx

/-- The logarithmic fourth likelihood jet exceeds `28` throughout the same compact scale band. -/
theorem twentyEight_lt_thetaCuspLikelihoodSourceLogPartitionJetFour_of_scale_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (23 / 6 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (31 / 8 : ℝ)) :
    28 < thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord :=
    thirty_lt_thetaCuspLikelihoodSourceOrdinaryJetFour_of_scale_mem hx hAlo hAhi
  have hretain := nineteenTwentieths_mul_ordinaryJetFour_lt_logJetFour hx
  calc
    (28 : ℝ) < (19 / 20 : ℝ) * 30 := by norm_num
    _ < (19 / 20 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by
      gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

end
end RHTower

