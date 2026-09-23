import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthCompactLowerBound

/-!
# Scale-fifteen-fourths affine lower bound for the fourth theta likelihood jet

On the short chamber `15/4 ≤ A ≤ 23/6`, the first atom-ray is kept with its live exponential
decay instead of frozen at the upper endpoint.  A sharper `13/25` fourth-score retention law and
the tangent inequality `1 - 3d ≤ exp (-3d)` then produce the affine logarithmic floor
`454 - 108 A < J₄`.  In weight coordinates `q = A - 3/2`, this is `292 - 108 q < J₄`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- At the scale-`15/4` support edge, thirteen twenty-fifths of the leading fourth monomial
survive. -/
theorem thirteenTwentyFifths_mul_pow_four_le_thetaLikelihoodFourthScore
    {z : ℝ} (hz : (45 / 4 : ℝ) ≤ z) :
    (13 / 25 : ℝ) * z ^ (4 : ℕ) ≤ thetaLikelihoodFourthScore z := by
  let y := z - 45 / 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  rw [show z = 45 / 4 + y by dsimp only [y]; ring]
  dsimp [thetaLikelihoodFourthScore]
  ring_nf
  have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  nlinarith

private theorem integrable_thetaLikelihoodFourthScore_tilted_scaleFifteenFourths
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

private theorem integral_thetaLikelihoodFourthScore_tilted_eq_scaleFifteenFourths
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

/-- The sharper support-edge law transfers to the complete ordinary fourth source jet. -/
theorem twoHundredEightTwentyFifths_mul_scale_pow_four_momentFour_le_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (208 / 25 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 ≤
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hI4 := integrable_thetaLikelihoodFourthScore_tilted_scaleFifteenFourths A hB
  have hlead : Integrable (fun t : ℝ =>
      (13 / 25 : ℝ) * A ^ (4 : ℕ) * t ^ (4 : ℕ))
      (thetaCuspHigherLikelihoodTiltedMeasure B) :=
    (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul _
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure B,
      (13 / 25 : ℝ) * A ^ (4 : ℕ) * t ^ (4 : ℕ) ≤ thetaLikelihoodFourthScore (A * t) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    have hAt : (45 / 4 : ℝ) ≤ A * t := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ t),
        mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 15 / 4)]
    have h := thirteenTwentyFifths_mul_pow_four_le_thetaLikelihoodFourthScore hAt
    calc
      (13 / 25 : ℝ) * A ^ (4 : ℕ) * t ^ (4 : ℕ) = (13 / 25 : ℝ) * (A * t) ^ (4 : ℕ) := by ring
      _ ≤ thetaLikelihoodFourthScore (A * t) := h
  have hint := integral_mono_ae hlead hI4 hpoint
  rw [integral_const_mul,
    integral_thetaLikelihoodFourthScore_tilted_eq_scaleFifteenFourths A hB] at hint
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hcoeff : 0 ≤ 16 / P := div_nonneg (by norm_num) hP.le
  have hscaled := mul_le_mul_of_nonneg_left hint hcoeff
  calc
    (208 / 25 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 =
      (16 / P) * ((13 / 25 : ℝ) * A ^ (4 : ℕ) *
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

/-- Sharp enough elementary rational lower enclosure at the scale-`15/4` endpoint. -/
theorem oneOverSeventySevenThousand_lt_exp_neg_fortyFiveFourths :
    (1 / 77000 : ℝ) < Real.exp (-(45 / 4 : ℝ)) := by
  have hpow11 : Real.exp 1 ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h11 : Real.exp 11 < (59900 : ℝ) := by
    rw [show (11 : ℝ) = (11 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow11.trans (by norm_num)
  have hsmall := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 1 / 256 by norm_num) (show (1 / 256 : ℝ) < 1 by norm_num)
  have hpow64 := pow_le_pow_left₀ (Real.exp_pos (1 / 256 : ℝ)).le hsmall 64
  have hquarter : Real.exp (1 / 4 : ℝ) < (257 / 200 : ℝ) := by
    rw [show (1 / 4 : ℝ) = (64 : ℕ) * (1 / 256 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact hpow64.trans_lt (by norm_num)
  have hupper : Real.exp (45 / 4 : ℝ) < 77000 := by
    rw [show (45 / 4 : ℝ) = 11 + 1 / 4 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 11, Real.exp_pos (1 / 4 : ℝ)]
  have hprod : Real.exp (-(45 / 4 : ℝ)) * Real.exp (45 / 4 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_lt_mul_of_pos_left hupper (Real.exp_pos (-(45 / 4 : ℝ)))
  rw [hprod] at hmul
  nlinarith

/-- Rational lower polynomial for the first atom-ray fourth moment. -/
def thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor : ℝ :=
  1296 + 18 * (81 * (3 / 7 : ℝ) + 108 * (3 / 7 : ℝ) ^ (2 : ℕ) +
    108 * (3 / 7 : ℝ) ^ (3 : ℕ) + 72 * (3 / 7 : ℝ) ^ (4 : ℕ) +
    24 * (3 / 7 : ℝ) ^ (5 : ℕ))

/-- Live affine lower envelope for the first atom-ray exponential across the short chamber. -/
theorem thetaCuspLikelihoodFourthScaleFifteenFourths_expAffine_lt_exp_neg_three_mul
    {A : ℝ} (hAlo : (15 / 4 : ℝ) ≤ A) (hAhi : A ≤ 23 / 6) :
    (1 / 77000 : ℝ) * (1 - 3 * (A - 15 / 4)) < Real.exp (-3 * A) := by
  let d := A - 15 / 4
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 12 := by dsimp only [d]; linarith
  have hfactor : 0 < 1 - 3 * d := by linarith
  have hfirst :
      (1 / 77000 : ℝ) * (1 - 3 * d) <
        Real.exp (-(45 / 4 : ℝ)) * (1 - 3 * d) :=
    mul_lt_mul_of_pos_right oneOverSeventySevenThousand_lt_exp_neg_fortyFiveFourths
      hfactor
  have hlinear : 1 - 3 * d ≤ Real.exp (-(3 * d)) :=
    Real.one_sub_le_exp_neg (3 * d)
  calc
    (1 / 77000 : ℝ) * (1 - 3 * (A - 15 / 4)) =
        (1 / 77000 : ℝ) * (1 - 3 * d) := by rfl
    _ < Real.exp (-(45 / 4 : ℝ)) * (1 - 3 * d) := hfirst
    _ ≤ Real.exp (-(45 / 4 : ℝ)) * Real.exp (-(3 * d)) := by gcongr
    _ = Real.exp (-3 * A) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring

/-- The exact first atom-ray fourth moment dominates its live affine scale envelope. -/
theorem thetaCuspLikelihoodFourthScaleFifteenFourthsAtomFloor_lt_dominantAtomMomentFour
    {A B : ℝ} (hAlo : (15 / 4 : ℝ) ≤ A) (hAhi : A ≤ 23 / 6)
    (hBA : B = A - 3 / 2) :
    (1 / 77000 : ℝ) * (1 - 3 * (A - 15 / 4)) *
        thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hBupper : B ≤ (7 / 3 : ℝ) := by rw [hBA]; linarith
  have hinv1 : (3 / 7 : ℝ) ≤ 1 / B := by
    have h := one_div_le_one_div_of_le hB hBupper
    norm_num at h ⊢
    exact h
  have hinv2 : (3 / 7 : ℝ) ^ (2 : ℕ) ≤ 1 / B ^ (2 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 2
    have h := one_div_le_one_div_of_le (pow_pos hB 2) hp
    norm_num at h ⊢
    exact h
  have hinv3 : (3 / 7 : ℝ) ^ (3 : ℕ) ≤ 1 / B ^ (3 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 3
    have h := one_div_le_one_div_of_le (pow_pos hB 3) hp
    norm_num at h ⊢
    exact h
  have hinv4 : (3 / 7 : ℝ) ^ (4 : ℕ) ≤ 1 / B ^ (4 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 4
    have h := one_div_le_one_div_of_le (pow_pos hB 4) hp
    norm_num at h ⊢
    exact h
  have hinv5 : (3 / 7 : ℝ) ^ (5 : ℕ) ≤ 1 / B ^ (5 : ℕ) := by
    have hp := pow_le_pow_left₀ hB.le hBupper 5
    have h := one_div_le_one_div_of_le (pow_pos hB 5) hp
    norm_num at h ⊢
    exact h
  let Q := 1296 + 18 *
    (81 / B + 108 / B ^ (2 : ℕ) + 108 / B ^ (3 : ℕ) + 72 / B ^ (4 : ℕ) + 24 / B ^ (5 : ℕ))
  have hQ : thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor ≤ Q := by
    dsimp only [thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor, Q]
    simp only [div_eq_mul_inv] at hinv1 hinv2 hinv3 hinv4 hinv5 ⊢
    nlinarith
  have hQpos : 0 < thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor := by
    norm_num [thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor]
  have hexp :=
    thetaCuspLikelihoodFourthScaleFifteenFourths_expAffine_lt_exp_neg_three_mul
      hAlo hAhi
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
  change (1 / 77000 : ℝ) * (1 - 3 * (A - 15 / 4)) *
      thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor <
    Real.exp (-3 * A) * Q
  calc
    _ < Real.exp (-3 * A) *
        thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor := by
      exact mul_lt_mul_of_pos_right hexp hQpos
    _ ≤ Real.exp (-3 * A) * Q := by gcongr

/-- Exact polynomial certificate converting the live atom envelope into the affine ordinary-jet
target. -/
theorem twentyNineteenths_mul_fourthAffineFloor_lt_atomEnvelope
    {A : ℝ} (hAlo : (15 / 4 : ℝ) ≤ A) (hAhi : A ≤ 23 / 6) :
    (20 / 19 : ℝ) * (454 - 108 * A) <
      (208 / 25 : ℝ) * A ^ (4 : ℕ) * (399 / 400 : ℝ) *
        ((1 / 77000 : ℝ) * (1 - 3 * (A - 15 / 4))) *
        thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor := by
  let y := 23 / 6 - A
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 12 := by dsimp only [y]; linarith
  rw [show A = 23 / 6 - y by dsimp only [y]; ring]
  dsimp [thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor]
  ring_nf
  have hy2 : y ^ (2 : ℕ) ≤ (1 / 12 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hy hyhi 2
  have hy4 : y ^ (4 : ℕ) ≤ (1 / 12 : ℝ) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hy hyhi 4
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy5 : 0 ≤ y ^ (5 : ℕ) := by positivity
  norm_num at hy2 hy4 ⊢
  nlinarith

/-- The ordinary fourth likelihood score dominates the live affine floor on
`15/4 ≤ A ≤ 23/6`. -/
theorem twentyNineteenths_mul_fourthAffineFloor_lt_thetaCuspLikelihoodSourceOrdinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 23 / 6) :
    (20 / 19 : ℝ) *
        (454 - 108 * thetaCuspSingleAtomReflectionScale 1 x) <
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let atomFloor := (1 / 77000 : ℝ) * (1 - 3 * (A - 15 / 4)) *
    thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hAtom : atomFloor <
      ∫ t : ℝ, t ^ (4 : ℕ) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2 := by
    dsimp only [atomFloor]
    exact thetaCuspLikelihoodFourthScaleFifteenFourthsAtomFloor_lt_dominantAtomMomentFour
      (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hfloor : 0 < atomFloor := by
    have hfactor : 0 < 1 - 3 * (A - 15 / 4) := by
      dsimp only [A] at hAhi ⊢
      linarith
    have hQ : 0 < thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor := by
      norm_num [thetaCuspLikelihoodFourthScaleFifteenFourthsAtomQFloor]
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
    twoHundredEightTwentyFifths_mul_scale_pow_four_momentFour_le_ordinaryJetFour
      hx hAlo
  have hpoly := twentyNineteenths_mul_fourthAffineFloor_lt_atomEnvelope
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hApos : 0 < A := by dsimp only [A] at hAlo ⊢; linarith
  calc
    (20 / 19 : ℝ) *
        (454 - 108 * thetaCuspSingleAtomReflectionScale 1 x) <
      (208 / 25 : ℝ) * A ^ (4 : ℕ) * (399 / 400 : ℝ) * atomFloor := by
        convert hpoly using 1 <;> dsimp only [A, atomFloor] <;> ring
    _ < (208 / 25 : ℝ) * A ^ (4 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment B 4 := by
      have hcoeff : 0 < (208 / 25 : ℝ) * A ^ (4 : ℕ) := by positivity
      nlinarith
    _ ≤ thetaCuspLikelihoodSourceOrdinaryJetFour x := by
      simpa only [A, B] using hbase

/-- Scale-dependent logarithmic fourth-jet floor on the new compact chamber. -/
theorem fourthAffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 23 / 6) :
    454 - 108 * thetaCuspSingleAtomReflectionScale 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hord :=
    twentyNineteenths_mul_fourthAffineFloor_lt_thetaCuspLikelihoodSourceOrdinaryJetFour
      hx hAlo hAhi
  have hretain := nineteenTwentieths_mul_ordinaryJetFour_lt_logJetFour hx
  calc
    454 - 108 * thetaCuspSingleAtomReflectionScale 1 x =
        (19 / 20 : ℝ) * ((20 / 19 : ℝ) *
          (454 - 108 * thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ < (19 / 20 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by gcongr
    _ < thetaCuspLikelihoodSourceLogPartitionJetFour x := hretain

/-- Weight-coordinate form of the affine fourth-jet floor: `292 - 108q < J₄`. -/
theorem fourthAffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 23 / 6) :
    292 - 108 * thetaCuspBornWittenWeight 1 x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := fourthAffineFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1 <;> ring

end
end RHTower
