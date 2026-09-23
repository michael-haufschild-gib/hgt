import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthScaleOneHundredSeventyNineFortyEighthsAffineLower

/-!
# Scale-89/24 affine lower bound for fourth theta likelihood jet

On `89/24 ≤ A ≤ 179/48`, the support law `51z⁴/100 ≤ score₄(z)` and live first
atom-ray floor prove `588 - 144A < J₄`, equivalently `372 - 144q < J₄`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Fifty-one hundredths of fourth leading monomial survive already at `z ≥ 89/8`. -/
theorem fiftyOneHundredths_mul_pow_four_le_thetaLikelihoodFourthScore_of_89Over24_support
    {z : ℝ} (hz : (89 / 8 : ℝ) ≤ z) :
    (51 / 100 : ℝ) * z ^ (4 : ℕ) ≤ thetaLikelihoodFourthScore z := by
  let y := z - 89 / 8
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  rw [show z = 89 / 8 + y by dsimp only [y]; ring]
  dsimp [thetaLikelihoodFourthScore]
  ring_nf
  have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  nlinarith

/-- Support-edge law transfers to complete ordinary fourth source jet from scale `89/24`. -/
theorem twoHundredFourTwentyFifths_mul_scale_pow_four_momentFour_le_ordinaryJetFour_of_89Over24_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (89 / 24 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (204 / 25 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 ≤
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate x),
      (51 / 100 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) * t ^ (4 : ℕ) ≤
        thetaLikelihoodFourthScore (thetaCuspSingleAtomReflectionScale 1 x * t) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate x)] with t ht
    have hAt : (89 / 8 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x * t := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ t),
        mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 89 / 24)]
    have h :=
      fiftyOneHundredths_mul_pow_four_le_thetaLikelihoodFourthScore_of_89Over24_support hAt
    calc
      (51 / 100 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) * t ^ (4 : ℕ) =
          (51 / 100 : ℝ) * (thetaCuspSingleAtomReflectionScale 1 x * t) ^ (4 : ℕ) := by ring
      _ ≤ thetaLikelihoodFourthScore (thetaCuspSingleAtomReflectionScale 1 x * t) := h
  have h := sixteen_mul_scale_pow_four_momentFour_le_ordinaryJetFour_of_ae_score_lower
    (51 / 100 : ℝ) hx hpoint
  convert h using 1 <;> ring

/-- Rational lower enclosure at scale `89/24`. -/
theorem oneOverSixtyEightThousand_lt_exp_neg_eightyNineEighths :
    (1 / 68000 : ℝ) < Real.exp (-(89 / 8 : ℝ)) := by
  have hpow11 : Real.exp 1 ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h11 : Real.exp 11 < (59900 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hsmall := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 1 / 128 by norm_num) (show (1 / 128 : ℝ) < 1 by norm_num)
  have hpow16 := pow_le_pow_left₀ (Real.exp_pos (1 / 128 : ℝ)).le hsmall 16
  have honeEighth : Real.exp (1 / 8 : ℝ) < (680 / 599 : ℝ) := by
    rw [show (1 / 8 : ℝ) = (16 : ℕ) * (1 / 128 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact hpow16.trans_lt (by norm_num)
  have hupper : Real.exp (89 / 8 : ℝ) < 68000 := by
    rw [show (89 / 8 : ℝ) = 11 + 1 / 8 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 11, Real.exp_pos (1 / 8 : ℝ)]
  have hprod : Real.exp (-(89 / 8 : ℝ)) * Real.exp (89 / 8 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_lt_mul_of_pos_left hupper (Real.exp_pos (-(89 / 8 : ℝ)))
  rw [hprod] at hmul
  nlinarith

/-- Live affine lower exponential envelope on the new chamber. -/
theorem thetaCuspLikelihoodFourthScale89Over24_expAffine_lt_exp_neg_three_mul
    {A : ℝ} (hAlo : (89 / 24 : ℝ) ≤ A) (hAhi : A ≤ 179 / 48) :
    (1 / 68000 : ℝ) * (1 - 3 * (A - 89 / 24)) < Real.exp (-3 * A) := by
  let d := A - 89 / 24
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d]; linarith
  have hfactor : 0 < 1 - 3 * d := by linarith
  have hfirst : (1 / 68000 : ℝ) * (1 - 3 * d) <
      Real.exp (-(89 / 8 : ℝ)) * (1 - 3 * d) :=
    mul_lt_mul_of_pos_right oneOverSixtyEightThousand_lt_exp_neg_eightyNineEighths hfactor
  have hlinear : 1 - 3 * d ≤ Real.exp (-(3 * d)) := Real.one_sub_le_exp_neg (3 * d)
  calc
    (1 / 68000 : ℝ) * (1 - 3 * (A - 89 / 24)) =
        (1 / 68000 : ℝ) * (1 - 3 * d) := by rfl
    _ < Real.exp (-(89 / 8 : ℝ)) * (1 - 3 * d) := hfirst
    _ ≤ Real.exp (-(89 / 8 : ℝ)) * Real.exp (-(3 * d)) := by gcongr
    _ = Real.exp (-3 * A) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring

/-- First atom-ray fourth moment dominates live scale envelope. -/
theorem thetaCuspLikelihoodFourthScale89Over24AtomFloor_lt_dominantAtomMomentFour
    {A B : ℝ} (hAlo : (89 / 24 : ℝ) ≤ A) (hAhi : A ≤ 179 / 48)
    (hBA : B = A - 3 / 2) :
    (1 / 68000 : ℝ) * (1 - 3 * (A - 89 / 24)) *
        thetaCuspLikelihoodFourthScale359Over96AtomQFloor <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hBupper : B ≤ (9 / 4 : ℝ) := by rw [hBA]; linarith
  have hinv1 : (4 / 9 : ℝ) ≤ 1 / B := by
    have h := one_div_le_one_div_of_le hB hBupper
    norm_num at h ⊢
    exact h
  have hinv2 : (4 / 9 : ℝ) ^ (2 : ℕ) ≤ 1 / B ^ (2 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 2
    have h := one_div_le_one_div_of_le (pow_pos hB 2) hp
    norm_num at h ⊢
    exact h
  have hinv3 : (4 / 9 : ℝ) ^ (3 : ℕ) ≤ 1 / B ^ (3 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 3
    have h := one_div_le_one_div_of_le (pow_pos hB 3) hp
    norm_num at h ⊢
    exact h
  have hinv4 : (4 / 9 : ℝ) ^ (4 : ℕ) ≤ 1 / B ^ (4 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 4
    have h := one_div_le_one_div_of_le (pow_pos hB 4) hp
    norm_num at h ⊢
    exact h
  have hinv5 : (4 / 9 : ℝ) ^ (5 : ℕ) ≤ 1 / B ^ (5 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 5
    have h := one_div_le_one_div_of_le (pow_pos hB 5) hp
    norm_num at h ⊢
    exact h
  let Q := 1296 + 18 *
    (81 / B + 108 / B ^ (2 : ℕ) + 108 / B ^ (3 : ℕ) + 72 / B ^ (4 : ℕ) + 24 / B ^ (5 : ℕ))
  have hQ : thetaCuspLikelihoodFourthScale359Over96AtomQFloor ≤ Q := by
    dsimp only [thetaCuspLikelihoodFourthScale359Over96AtomQFloor, Q]
    simp only [div_eq_mul_inv] at hinv1 hinv2 hinv3 hinv4 hinv5 ⊢
    nlinarith
  have hQpos : 0 < thetaCuspLikelihoodFourthScale359Over96AtomQFloor := by
    norm_num [thetaCuspLikelihoodFourthScale359Over96AtomQFloor]
  have hexp := thetaCuspLikelihoodFourthScale89Over24_expAffine_lt_exp_neg_three_mul
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
  change (1 / 68000 : ℝ) * (1 - 3 * (A - 89 / 24)) *
      thetaCuspLikelihoodFourthScale359Over96AtomQFloor < Real.exp (-3 * A) * Q
  calc
    _ < Real.exp (-3 * A) * thetaCuspLikelihoodFourthScale359Over96AtomQFloor := by
      exact mul_lt_mul_of_pos_right hexp hQpos
    _ ≤ Real.exp (-3 * A) * Q := by gcongr

/-- Cleared polynomial converting atom envelope to affine ordinary-jet target. -/
theorem twentyNineteenths_mul_fourth89Over24AffineFloor_lt_atomEnvelope
    {A : ℝ} (hAlo : (89 / 24 : ℝ) ≤ A) (hAhi : A ≤ 179 / 48) :
    (20 / 19 : ℝ) * (588 - 144 * A) <
      (204 / 25 : ℝ) * A ^ (4 : ℕ) * (399 / 400 : ℝ) *
        ((1 / 68000 : ℝ) * (1 - 3 * (A - 89 / 24))) *
        thetaCuspLikelihoodFourthScale359Over96AtomQFloor := by
  let y := A - 89 / 24
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 48 := by dsimp only [y]; linarith
  rw [show A = 89 / 24 + y by dsimp only [y]; ring]
  dsimp [thetaCuspLikelihoodFourthScale359Over96AtomQFloor]
  ring_nf
  have hy2 : y ^ (2 : ℕ) ≤ (1 / 48 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hy hyhi 2
  have hy3 : y ^ (3 : ℕ) ≤ (1 / 48 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hy hyhi 3
  have hy4 : y ^ (4 : ℕ) ≤ (1 / 48 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hy hyhi 4
  have hy5 : 0 ≤ y ^ (5 : ℕ) := by positivity
  norm_num at hy2 hy3 hy4 ⊢
  nlinarith

/-- Ordinary fourth score dominates moving floor. -/
theorem twentyNineteenths_mul_fourth89Over24AffineFloor_lt_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (89 / 24 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 179 / 48) :
    (20 / 19 : ℝ) * (588 - 144 * thetaCuspSingleAtomReflectionScale 1 x) <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let atomFloor := (1 / 68000 : ℝ) * (1 - 3 * (A - 89 / 24)) *
    thetaCuspLikelihoodFourthScale359Over96AtomQFloor
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hAtom : atomFloor <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
    dsimp only [atomFloor]
    exact thetaCuspLikelihoodFourthScale89Over24AtomFloor_lt_dominantAtomMomentFour
      (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hfloor : 0 < atomFloor := by
    have hfactor : 0 < 1 - 3 * (A - 89 / 24) := by
      dsimp only [A] at hAhi ⊢
      linarith
    have hQ : 0 < thetaCuspLikelihoodFourthScale359Over96AtomQFloor := by
      norm_num [thetaCuspLikelihoodFourthScale359Over96AtomQFloor]
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
    twoHundredFourTwentyFifths_mul_scale_pow_four_momentFour_le_ordinaryJetFour_of_89Over24_le
      hx hAlo
  have hpoly := twentyNineteenths_mul_fourth89Over24AffineFloor_lt_atomEnvelope
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hApos : 0 < A := by dsimp only [A] at hAlo ⊢; linarith
  calc
    (20 / 19 : ℝ) * (588 - 144 * thetaCuspSingleAtomReflectionScale 1 x) <
      (204 / 25 : ℝ) * A ^ (4 : ℕ) * (399 / 400 : ℝ) * atomFloor := by
        convert hpoly using 1 <;> dsimp only [A, atomFloor] <;> ring
    _ < (204 / 25 : ℝ) * A ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment B 4 := by
      have hcoeff : 0 < (204 / 25 : ℝ) * A ^ (4 : ℕ) := by positivity
      nlinarith
    _ ≤ thetaCuspLikelihoodSourceOrdinaryJetFour x := by
      simpa only [A, B] using hbase

/-- Logarithmic fourth-jet floor on `89/24 ≤ A ≤ 179/48`. -/
theorem fourth89Over24AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (89 / 24 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 179 / 48) :
    588 - 144 * thetaCuspSingleAtomReflectionScale 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord := twentyNineteenths_mul_fourth89Over24AffineFloor_lt_ordinaryJetFour
    hx hAlo hAhi
  have hretain := nineteenTwentieths_mul_ordinaryJetFour_lt_logJetFour hx
  calc
    588 - 144 * thetaCuspSingleAtomReflectionScale 1 x =
        (19 / 20 : ℝ) * ((20 / 19 : ℝ) *
          (588 - 144 * thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ < (19 / 20 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

/-- Weight-coordinate form: `372 - 144q < J₄`. -/
theorem fourth89Over24AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (89 / 24 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 179 / 48) :
    372 - 144 * thetaCuspBornWittenWeight 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := fourth89Over24AffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1 <;> ring

end
end RHTower
