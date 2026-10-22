import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodScaleLocalTailCooling

/-!
# Scale-59/16 affine lower bound for fourth theta likelihood jet

On `59/16 ≤ A ≤ 89/24`, a sharper support law, live first-atom ray floor, and the scale-local
`99/100` Bell-retention theorem prove `1300 - 336A < J₄`, equivalently
`796 - 336q < J₄`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Live first-atom Bell factor at the endpoint `B = 53/24`. -/
def thetaCuspLikelihoodFourthScale59Over16AtomQFloor : ℝ :=
  1296 + 18 *
    (81 * (24 / 53 : ℝ) + 108 * (24 / 53 : ℝ) ^ (2 : ℕ) +
      108 * (24 / 53 : ℝ) ^ (3 : ℕ) + 72 * (24 / 53 : ℝ) ^ (4 : ℕ) +
      24 * (24 / 53 : ℝ) ^ (5 : ℕ))

/-- `513/1000` of the leading fourth monomial survives already at `z ≥ 177/16`. -/
theorem fiveHundredThirteenThousandths_mul_pow_four_le_thetaLikelihoodFourthScore_of_59Over16_support
    {z : ℝ} (hz : (177 / 16 : ℝ) ≤ z) :
    (513 / 1000 : ℝ) * z ^ (4 : ℕ) ≤ thetaLikelihoodFourthScore z := by
  let y := z - 177 / 16
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  rw [show z = 177 / 16 + y by dsimp only [y]; ring]
  dsimp [thetaLikelihoodFourthScore]
  ring_nf
  have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  nlinarith

/-- Support-edge law transfers to the complete ordinary fourth source jet from scale `59/16`. -/
theorem oneThousandTwentySixOneHundredTwentyFifths_mul_scale_pow_four_momentFour_le_ordinaryJetFour_of_59Over16_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (1026 / 125 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 ≤
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate x),
      (513 / 1000 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) * t ^ (4 : ℕ) ≤
        thetaLikelihoodFourthScore (thetaCuspSingleAtomReflectionScale 1 x * t) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate x)] with t ht
    have hAt : (177 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x * t := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ t),
        mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 59 / 16)]
    have h :=
      fiveHundredThirteenThousandths_mul_pow_four_le_thetaLikelihoodFourthScore_of_59Over16_support
        hAt
    calc
      (513 / 1000 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) * t ^ (4 : ℕ) =
          (513 / 1000 : ℝ) * (thetaCuspSingleAtomReflectionScale 1 x * t) ^ (4 : ℕ) := by
        ring
      _ ≤ thetaLikelihoodFourthScore (thetaCuspSingleAtomReflectionScale 1 x * t) := h
  have h := sixteen_mul_scale_pow_four_momentFour_le_ordinaryJetFour_of_ae_score_lower
    (513 / 1000 : ℝ) hx hpoint
  convert h using 1 <;> ring

/-- Rational lower enclosure at scale `59/16`. -/
theorem oneOverSixtyThreeThousandSevenHundredFifty_lt_exp_neg_oneHundredSeventySevenSixteenths :
    (1 / 63750 : ℝ) < Real.exp (-(177 / 16 : ℝ)) := by
  have hpow11 : Real.exp 1 ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h11 : Real.exp 11 < (59875 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hsmall := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 1 / 512 by norm_num) (show (1 / 512 : ℝ) < 1 by norm_num)
  have hpow32 := pow_le_pow_left₀ (Real.exp_pos (1 / 512 : ℝ)).le hsmall 32
  have honeSixteenth : Real.exp (1 / 16 : ℝ) < (10647 / 10000 : ℝ) := by
    rw [show (1 / 16 : ℝ) = (32 : ℕ) * (1 / 512 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact hpow32.trans_lt (by norm_num)
  have hupper : Real.exp (177 / 16 : ℝ) < 63750 := by
    rw [show (177 / 16 : ℝ) = 11 + 1 / 16 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 11, Real.exp_pos (1 / 16 : ℝ)]
  have hprod : Real.exp (-(177 / 16 : ℝ)) * Real.exp (177 / 16 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_lt_mul_of_pos_left hupper (Real.exp_pos (-(177 / 16 : ℝ)))
  rw [hprod] at hmul
  nlinarith

/-- Live affine lower exponential envelope on the scale-`59/16` chamber. -/
theorem thetaCuspLikelihoodFourthScale59Over16_expAffine_lt_exp_neg_three_mul
    {A : ℝ} (hAlo : (59 / 16 : ℝ) ≤ A) (hAhi : A ≤ 89 / 24) :
    (1 / 63750 : ℝ) * (1 - 3 * (A - 59 / 16)) < Real.exp (-3 * A) := by
  let d := A - 59 / 16
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d]; linarith
  have hfactor : 0 < 1 - 3 * d := by linarith
  have hfirst : (1 / 63750 : ℝ) * (1 - 3 * d) <
      Real.exp (-(177 / 16 : ℝ)) * (1 - 3 * d) :=
    mul_lt_mul_of_pos_right
      oneOverSixtyThreeThousandSevenHundredFifty_lt_exp_neg_oneHundredSeventySevenSixteenths
      hfactor
  have hlinear : 1 - 3 * d ≤ Real.exp (-(3 * d)) := Real.one_sub_le_exp_neg (3 * d)
  calc
    (1 / 63750 : ℝ) * (1 - 3 * (A - 59 / 16)) =
        (1 / 63750 : ℝ) * (1 - 3 * d) := by rfl
    _ < Real.exp (-(177 / 16 : ℝ)) * (1 - 3 * d) := hfirst
    _ ≤ Real.exp (-(177 / 16 : ℝ)) * Real.exp (-(3 * d)) := by gcongr
    _ = Real.exp (-3 * A) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring

/-- First atom-ray fourth moment dominates the live scale-`59/16` envelope. -/
theorem thetaCuspLikelihoodFourthScale59Over16AtomFloor_lt_dominantAtomMomentFour
    {A B : ℝ} (hAlo : (59 / 16 : ℝ) ≤ A) (hAhi : A ≤ 89 / 24)
    (hBA : B = A - 3 / 2) :
    (1 / 63750 : ℝ) * (1 - 3 * (A - 59 / 16)) *
        thetaCuspLikelihoodFourthScale59Over16AtomQFloor <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hBupper : B ≤ (53 / 24 : ℝ) := by rw [hBA]; linarith
  have hinv1 : (24 / 53 : ℝ) ≤ 1 / B := by
    have h := one_div_le_one_div_of_le hB hBupper
    norm_num at h ⊢
    exact h
  have hinv2 : (24 / 53 : ℝ) ^ (2 : ℕ) ≤ 1 / B ^ (2 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 2
    have h := one_div_le_one_div_of_le (pow_pos hB 2) hp
    norm_num at h ⊢
    exact h
  have hinv3 : (24 / 53 : ℝ) ^ (3 : ℕ) ≤ 1 / B ^ (3 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 3
    have h := one_div_le_one_div_of_le (pow_pos hB 3) hp
    norm_num at h ⊢
    exact h
  have hinv4 : (24 / 53 : ℝ) ^ (4 : ℕ) ≤ 1 / B ^ (4 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 4
    have h := one_div_le_one_div_of_le (pow_pos hB 4) hp
    norm_num at h ⊢
    exact h
  have hinv5 : (24 / 53 : ℝ) ^ (5 : ℕ) ≤ 1 / B ^ (5 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 5
    have h := one_div_le_one_div_of_le (pow_pos hB 5) hp
    norm_num at h ⊢
    exact h
  let Q := 1296 + 18 *
    (81 / B + 108 / B ^ (2 : ℕ) + 108 / B ^ (3 : ℕ) + 72 / B ^ (4 : ℕ) + 24 / B ^ (5 : ℕ))
  have hQ : thetaCuspLikelihoodFourthScale59Over16AtomQFloor ≤ Q := by
    dsimp only [thetaCuspLikelihoodFourthScale59Over16AtomQFloor, Q]
    simp only [div_eq_mul_inv] at hinv1 hinv2 hinv3 hinv4 hinv5 ⊢
    nlinarith
  have hQpos : 0 < thetaCuspLikelihoodFourthScale59Over16AtomQFloor := by
    norm_num [thetaCuspLikelihoodFourthScale59Over16AtomQFloor]
  have hexp := thetaCuspLikelihoodFourthScale59Over16_expAffine_lt_exp_neg_three_mul
    hAlo hAhi
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
    (n := 2) (by norm_num) 4 hB]
  norm_num [thetaCuspLikelihoodGap, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  have hpref : Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(B * 3)) = Real.exp (-3 * A) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  rw [hpref]
  change (1 / 63750 : ℝ) * (1 - 3 * (A - 59 / 16)) *
      thetaCuspLikelihoodFourthScale59Over16AtomQFloor < Real.exp (-3 * A) * Q
  calc
    _ < Real.exp (-3 * A) * thetaCuspLikelihoodFourthScale59Over16AtomQFloor := by
      exact mul_lt_mul_of_pos_right hexp hQpos
    _ ≤ Real.exp (-3 * A) * Q := by gcongr

/-- Cleared polynomial converting the atom envelope to the affine ordinary-jet target. -/
theorem oneHundredNinetyNineths_mul_fourth59Over16AffineFloor_lt_atomEnvelope
    {A : ℝ} (hAlo : (59 / 16 : ℝ) ≤ A) (hAhi : A ≤ 89 / 24) :
    (100 / 99 : ℝ) * (1300 - 336 * A) <
      (1026 / 125 : ℝ) * A ^ (4 : ℕ) * (399 / 400 : ℝ) *
        ((1 / 63750 : ℝ) * (1 - 3 * (A - 59 / 16))) *
        thetaCuspLikelihoodFourthScale59Over16AtomQFloor := by
  let y := A - 59 / 16
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 48 := by dsimp only [y]; linarith
  rw [show A = 59 / 16 + y by dsimp only [y]; ring]
  dsimp [thetaCuspLikelihoodFourthScale59Over16AtomQFloor]
  ring_nf
  have hy2 : y ^ (2 : ℕ) ≤ (1 / 48 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hy hyhi 2
  have hy3 : y ^ (3 : ℕ) ≤ (1 / 48 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hy hyhi 3
  have hy4 : y ^ (4 : ℕ) ≤ (1 / 48 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hy hyhi 4
  have hy5 : 0 ≤ y ^ (5 : ℕ) := by positivity
  norm_num at hy2 hy3 hy4 ⊢
  nlinarith

/-- Ordinary fourth score dominates the moving floor on the scale-`59/16` chamber. -/
theorem oneHundredNinetyNineths_mul_fourth59Over16AffineFloor_lt_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 89 / 24) :
    (100 / 99 : ℝ) * (1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x) <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let atomFloor := (1 / 63750 : ℝ) * (1 - 3 * (A - 59 / 16)) *
    thetaCuspLikelihoodFourthScale59Over16AtomQFloor
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hAtom : atomFloor <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
    dsimp only [atomFloor]
    exact thetaCuspLikelihoodFourthScale59Over16AtomFloor_lt_dominantAtomMomentFour
      (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hfloor : 0 < atomFloor := by
    have hfactor : 0 < 1 - 3 * (A - 59 / 16) := by
      dsimp only [A] at hAhi ⊢
      linarith
    have hQ : 0 < thetaCuspLikelihoodFourthScale59Over16AtomQFloor := by
      norm_num [thetaCuspLikelihoodFourthScale59Over16AtomQFloor]
    dsimp only [atomFloor]
    positivity
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
  have hMoment : atomFloor < thetaCuspHigherLikelihoodSpectralMoment B 4 := by
    rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
    have hAtom' : atomFloor <
        ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-B * t)
          ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
      simpa only [neg_mul] using hAtom
    exact hAtom'.trans_le hMono
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
  have hNorm : (399 / 400 : ℝ) * atomFloor <
      thetaCuspLikelihoodNormalizedMoment B 4 := by
    have hfirst := mul_lt_mul_of_pos_right hPinv hfloor
    have hsecond := mul_lt_mul_of_pos_left hMoment (by positivity : (0 : ℝ) < 1 / P)
    unfold thetaCuspLikelihoodNormalizedMoment
    calc
      (399 / 400 : ℝ) * atomFloor < (1 / P) * atomFloor := hfirst
      _ < (1 / P) * thetaCuspHigherLikelihoodSpectralMoment B 4 := hsecond
      _ = thetaCuspHigherLikelihoodSpectralMoment B 4 / P := by ring
  have hbase :=
    oneThousandTwentySixOneHundredTwentyFifths_mul_scale_pow_four_momentFour_le_ordinaryJetFour_of_59Over16_le
      hx hAlo
  have hpoly := oneHundredNinetyNineths_mul_fourth59Over16AffineFloor_lt_atomEnvelope
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hApos : 0 < A := by dsimp only [A] at hAlo ⊢; linarith
  calc
    (100 / 99 : ℝ) * (1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x) <
      (1026 / 125 : ℝ) * A ^ (4 : ℕ) * (399 / 400 : ℝ) * atomFloor := by
        convert hpoly using 1 <;> dsimp only [A, atomFloor] <;> ring
    _ < (1026 / 125 : ℝ) * A ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment B 4 := by
      have hcoeff : 0 < (1026 / 125 : ℝ) * A ^ (4 : ℕ) := by positivity
      nlinarith
    _ ≤ thetaCuspLikelihoodSourceOrdinaryJetFour x := by
      simpa only [A, B] using hbase

/-- Logarithmic fourth-jet floor on `59/16 ≤ A ≤ 89/24`. -/
theorem fourth59Over16AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 89 / 24) :
    1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord := oneHundredNinetyNineths_mul_fourth59Over16AffineFloor_lt_ordinaryJetFour
    hx hAlo hAhi
  have hretain := ninetyNineHundredths_mul_ordinaryJetFour_lt_logJetFour_of_59Over16_le
    hx hAlo
  calc
    1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x =
        (99 / 100 : ℝ) * ((100 / 99 : ℝ) *
          (1300 - 336 * thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ < (99 / 100 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

/-- Weight-coordinate form: `796 - 336q < J₄`. -/
theorem fourth59Over16AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 89 / 24) :
    796 - 336 * thetaCuspBornWittenWeight 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := fourth59Over16AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1 <;> ring

end
end RHTower
