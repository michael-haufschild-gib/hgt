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
      (thetaCuspHigherLikelihoodTiltedMeasure B) := by
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (A ^ (4 : ℕ))
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (6 * A ^ (3 : ℕ))
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (7 * A ^ (2 : ℕ))
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  convert (((h4.sub h3).add h2).sub h1) using 1
  funext t
  dsimp [thetaLikelihoodFourthScore]
  ring

private theorem integral_thetaLikelihoodFourthScore_tilted_eq_lower
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t)
      ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        6 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        7 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (A ^ (4 : ℕ))
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (6 * A ^ (3 : ℕ))
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (7 * A ^ (2 : ℕ))
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ (4 : ℕ) * t ^ (4 : ℕ)
  let f3 : ℝ → ℝ := fun t => (6 * A ^ (3 : ℕ)) * t ^ (3 : ℕ)
  let f2 : ℝ → ℝ := fun t => (7 * A ^ (2 : ℕ)) * t ^ (2 : ℕ)
  let f1 : ℝ → ℝ := fun t => A * t ^ (1 : ℕ)
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t)) =
      ((f4 - f3) + f2) - f1 by
    funext t
    dsimp [thetaLikelihoodFourthScore, f4, f3, f2, f1]
    ring]
  rw [integral_sub' ((h4.sub h3).add h2) h1,
    integral_add' (h4.sub h3) h2, integral_sub' h4 h3]
  simp only [integral_const_mul]
  rfl

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
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ (2 : ℕ) * e2 - A * e1)
  let b3 := 8 * (A ^ (3 : ℕ) * e3 - 3 * A ^ (2 : ℕ) * e2 + A * e1)
  let b4 := thetaCuspLikelihoodSourceOrdinaryJetFour x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using three_lt_thetaCuspSingleAtomReflectionScale
      (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have he1 : 0 < e1 := by simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    simpa only [e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have hp : 0 < p := by
    have h22 := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    have h22' : e2 ^ (2 : ℕ) ≤ p * e4 := by
      simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h22
    nlinarith [sq_pos_of_pos he2]
  have h11 : e1 ^ (2 : ℕ) ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h13 : e1 * e3 ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 3
    simpa only [B, p, e1, e3, e4,
      thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 3 = 4 by norm_num] using h
  have h22 : e2 ^ (2 : ℕ) ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hb1 : 0 < b1 := by dsimp only [b1]; positivity
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right hA he2
    nlinarith
  have hb2 : 0 < b2 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b2]
    nlinarith
  have hb2Upper : b2 ≤ 4 * A ^ (2 : ℕ) * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have hb3Upper : b3 ≤ 8 * A ^ (3 : ℕ) * e3 := by
    dsimp only [b3]
    have hcross : A * e1 ≤ 3 * A ^ (2 : ℕ) * e2 := by
      have hleft : A * e1 ≤ A * (e2 / 3) := by
        apply mul_le_mul_of_nonneg_left (by linarith) hA0.le
      have hright : A * (e2 / 3) ≤ 3 * A ^ (2 : ℕ) * e2 := by
        nlinarith [mul_pos hA0 he2]
      exact hleft.trans hright
    nlinarith
  have hb4Lower : (32 / 5 : ℝ) * A ^ (4 : ℕ) * e4 ≤ b4 := by
    simpa only [A, B, e4, b4] using
      two_fifths_le_thetaCuspLikelihoodSourceOrdinaryJetFour hx
  have hb4 : 0 < b4 := lt_of_lt_of_le (by positivity) hb4Lower
  have hb1b3Core : b1 * b3 ≤ 16 * A ^ (4 : ℕ) * (e1 * e3) := by
    calc
      b1 * b3 ≤ (2 * A * e1) * (8 * A ^ (3 : ℕ) * e3) := by
        dsimp only [b1]
        gcongr
      _ = 16 * A ^ (4 : ℕ) * (e1 * e3) := by ring
  have hb1b3Moment : 16 * A ^ (4 : ℕ) * (e1 * e3) ≤ 16 * A ^ (4 : ℕ) * (p * e4) := by
    gcongr
  have hb1b3 : 4 * b1 * b3 ≤ 10 * p * b4 := by
    have hcore := hb1b3Core.trans hb1b3Moment
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower (by positivity : 0 ≤ 10 * p)
    nlinarith
  have hb2sqCore : b2 ^ (2 : ℕ) ≤ 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by
    have hupper0 : 0 ≤ 4 * A ^ (2 : ℕ) * e2 := by positivity
    have hpow := pow_le_pow_left₀ hb2.le hb2Upper 2
    calc
      b2 ^ (2 : ℕ) ≤ (4 * A ^ (2 : ℕ) * e2) ^ (2 : ℕ) := hpow
      _ = 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by ring
  have hb2sqMoment : 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) ≤ 16 * A ^ (4 : ℕ) * (p * e4) := by
    gcongr
  have hb2sq : 3 * b2 ^ (2 : ℕ) ≤ (15 / 2 : ℝ) * p * b4 := by
    have hcore := hb2sqCore.trans hb2sqMoment
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower
      (by positivity : 0 ≤ (15 / 2 : ℝ) * p)
    nlinarith
  have he1four : e1 ^ (4 : ℕ) ≤ p ^ (3 : ℕ) * e4 := by
    have h11sq := pow_le_pow_left₀ (sq_nonneg e1) h11 2
    have hp0 : 0 ≤ p := hp.le
    have hstep : (p * e2) ^ (2 : ℕ) ≤ p ^ (2 : ℕ) * (p * e4) := by
      rw [mul_pow]
      gcongr
    calc
      e1 ^ (4 : ℕ) = (e1 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ (p * e2) ^ (2 : ℕ) := h11sq
      _ ≤ p ^ (2 : ℕ) * (p * e4) := hstep
      _ = p ^ (3 : ℕ) * e4 := by ring
  have hb1four : 6 * b1 ^ (4 : ℕ) ≤ 15 * p ^ (3 : ℕ) * b4 := by
    have hcore : 6 * b1 ^ (4 : ℕ) ≤ 96 * A ^ (4 : ℕ) * (p ^ (3 : ℕ) * e4) := by
      dsimp only [b1]
      have hscaled := mul_le_mul_of_nonneg_left he1four
        (by positivity : 0 ≤ 96 * A ^ (4 : ℕ))
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower
      (by positivity : 0 ≤ 15 * p ^ (3 : ℕ))
    nlinarith
  have hcoeff : (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 1 / 20 := by
    have hpUpper : p < (1 / 400 : ℝ) := by linarith
    have hp3 : p ^ (3 : ℕ) < (1 / 400 : ℝ) ^ (3 : ℕ) :=
      pow_lt_pow_left₀ hpUpper hp.le (by norm_num)
    have hlinear : (35 / 2 : ℝ) * p < 35 / 800 := by
      have h := mul_lt_mul_of_pos_left hpUpper (by norm_num : (0 : ℝ) < 35 / 2)
      norm_num at h ⊢
      exact h
    have hcubic : 15 * p ^ (3 : ℕ) < (15 / 64000000 : ℝ) := by
      have h := mul_lt_mul_of_pos_left hp3 (by norm_num : (0 : ℝ) < 15)
      norm_num at h ⊢
      exact h
    calc
      (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 35 / 800 + 15 / 64000000 :=
        add_lt_add hlinear hcubic
      _ < 1 / 20 := by norm_num
  have hloss :
      4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) < (1 / 20 : ℝ) * b4 := by
    have hsum :
        4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) ≤
          ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ)) * b4 := by
      calc
        4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) ≤
            10 * p * b4 + (15 / 2 : ℝ) * p * b4 + 15 * p ^ (3 : ℕ) * b4 :=
          add_le_add (add_le_add hb1b3 hb2sq) hb1four
        _ = ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ)) * b4 := by ring
    exact lt_of_le_of_lt hsum (mul_lt_mul_of_pos_right hcoeff hb4)
  have hdecomp :
      thetaCuspLikelihoodSourceLogPartitionJetFour x =
        b4 - 4 * b1 * b3 - 3 * b2 ^ (2 : ℕ) + 12 * b1 ^ (2 : ℕ) * b2 - 6 * b1 ^ (4 : ℕ) := by
    dsimp only [b1, b2, b3, b4, A, B, e1, e2, e3, e4]
    unfold thetaCuspLikelihoodSourceOrdinaryJetFour
      thetaCuspLikelihoodSourceLogPartitionJetFour thetaCuspLikelihoodFourthCumulant
      thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
    ring
  rw [hdecomp]
  have hpositive : 0 < 12 * b1 ^ (2 : ℕ) * b2 := by positivity
  nlinarith

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

