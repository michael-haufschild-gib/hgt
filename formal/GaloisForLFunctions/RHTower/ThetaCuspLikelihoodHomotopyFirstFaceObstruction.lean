import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopyBoseBernsteinCone
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopySeamRatioOrientation

/-!
# First-face obstruction for the C5 likelihood homotopy

The first atom and literal higher-likelihood cumulants force a positive seventh-order
coefficient in the first lowest-mode-shifted Bose face once the structural scale reaches six.
This is the exact source obstruction used to decide the shifted-cone route.

RH chain tested: shifted Bose cone -> positive M''' -> convex likelihood lift -> direct-J ->
rank-four/Ptolemy -> CLG/TTF or Weil positivity -> RH.
-/

open scoped BigOperators ContDiff

namespace RHTower

noncomputable section

private theorem reflectionScale_one_eq_morseScale (u : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 u = thetaCuspMorseScale 1 u := by
  unfold thetaCuspSingleAtomReflectionScale thetaCuspMorseScale
  rw [show (2 : ℝ) * u = u + u by ring, Real.exp_add]
  norm_num
  ring

theorem thetaCuspC5FirstFaceAtomBounds
    {u : ℝ} (hu : 0 ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    6 * thetaCuspSingleAtomReflectionScale 1 u <
        thetaCuspBornWittenLogThirdDerivative 1 u ∧
      thetaCuspBornWittenLogFourthDerivative 1 u <
        2 * thetaCuspSingleAtomReflectionScale 1 u *
          thetaCuspBornWittenLogThirdDerivative 1 u ∧
      thetaCuspBornWittenLogFifthDerivative 1 u <
        16 * thetaCuspSingleAtomReflectionScale 1 u ^ 2 *
          thetaCuspBornWittenLogThirdDerivative 1 u := by
  let q := thetaCuspBornWittenWeight 1 u
  let S := thetaCuspSingleAtomReflectionScale 1 u
  have hq : 0 < q := by
    simpa only [q] using thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hu
  have hSq : S = q + 3 / 2 := by
    dsimp only [S, q]
    rw [reflectionScale_one_eq_morseScale, thetaCuspBornWittenWeight_eq]
    ring
  have hq45 : (9 / 2 : ℝ) ≤ q := by
    change 6 ≤ S at hscale
    rw [hSq] at hscale
    linarith
  let r := q - 9 / 2
  have hr : 0 ≤ r := by dsimp only [r]; linarith
  have hpnum : 0 < q ^ 3 - 6 * q - 18 := by
    rw [show q ^ 3 - 6 * q - 18 =
        r ^ 3 + (27 / 2 : ℝ) * r ^ 2 + (219 / 4 : ℝ) * r + 369 / 8 by
      dsimp only [r]
      ring]
    positivity
  have hbnum : 0 < 8 * q ^ 4 - 12 * q ^ 2 - 108 * q - 162 := by
    rw [show 8 * q ^ 4 - 12 * q ^ 2 - 108 * q - 162 =
        8 * r ^ 4 + 144 * r ^ 3 + 960 * r ^ 2 + 2700 * r + 4779 / 2 by
      dsimp only [r]
      ring]
    positivity
  have hpbr : 3 < 4 - 6 / q ^ 2 - 18 / q ^ 3 := by
    rw [← sub_pos]
    rw [show 4 - 6 / q ^ 2 - 18 / q ^ 3 - 3 =
        (q ^ 3 - 6 * q - 18) / q ^ 3 by
      field_simp [hq.ne']
      ring]
    exact div_pos hpnum (pow_pos hq 3)
  have hbbr : 8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4 < 16 := by
    rw [← sub_pos]
    rw [show 16 - (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4) =
        (8 * q ^ 4 - 12 * q ^ 2 - 108 * q - 162) / q ^ 4 by
      field_simp [hq.ne']
      ring]
    exact div_pos hbnum (pow_pos hq 4)
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) hscale
  let B := 8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4
  let P := 4 - 6 / q ^ 2 - 18 / q ^ 3
  have hB : B < 16 := by simpa only [B] using hbbr
  have hP : 3 < P := by simpa only [P] using hpbr
  have h2S : 0 < 2 * S := mul_pos (by norm_num) hS
  have hthird : 6 * S < thetaCuspBornWittenLogThirdDerivative 1 u := by
    unfold thetaCuspBornWittenLogThirdDerivative
    change 6 * S < (2 * q + 3) * P
    rw [show 2 * q + 3 = 2 * S by rw [hSq]; ring]
    have hPscaled : (2 * S) * 3 < (2 * S) * P :=
      mul_lt_mul_of_pos_left hP h2S
    convert hPscaled using 1
    all_goals ring
  have hfourth : thetaCuspBornWittenLogFourthDerivative 1 u <
      2 * S * thetaCuspBornWittenLogThirdDerivative 1 u := by
    unfold thetaCuspBornWittenLogFourthDerivative
    change (2 * q + 3) * B <
      2 * S * thetaCuspBornWittenLogThirdDerivative 1 u
    rw [show 2 * q + 3 = 2 * S by rw [hSq]; ring]
    have hleft : (2 * S) * B < (2 * S) * 16 :=
      mul_lt_mul_of_pos_left hB h2S
    have h16 : (16 : ℝ) < thetaCuspBornWittenLogThirdDerivative 1 u := by
      have : (16 : ℝ) < 6 * S := by linarith
      exact this.trans hthird
    exact hleft.trans (mul_lt_mul_of_pos_left h16 h2S)
  have hC :
      16 - 24 / q ^ 2 - 504 / q ^ 3 - 1944 / q ^ 4 - 1944 / q ^ 5 < 16 := by
    have h2 : 0 < 24 / q ^ 2 := div_pos (by norm_num) (pow_pos hq 2)
    have h3 : 0 < 504 / q ^ 3 := div_pos (by norm_num) (pow_pos hq 3)
    have h4 : 0 < 1944 / q ^ 4 := div_pos (by norm_num) (pow_pos hq 4)
    have h5 : 0 < 1944 / q ^ 5 := div_pos (by norm_num) (pow_pos hq 5)
    linarith
  have hfifthUpper : thetaCuspBornWittenLogFifthDerivative 1 u < 32 * S := by
    unfold thetaCuspBornWittenLogFifthDerivative
    change (2 * q + 3) *
        (16 - 24 / q ^ 2 - 504 / q ^ 3 - 1944 / q ^ 4 - 1944 / q ^ 5) < 32 * S
    rw [show 2 * q + 3 = 2 * S by rw [hSq]; ring]
    calc
      (2 * S) *
          (16 - 24 / q ^ 2 - 504 / q ^ 3 - 1944 / q ^ 4 - 1944 / q ^ 5) <
          (2 * S) * 16 := mul_lt_mul_of_pos_left hC h2S
      _ = 32 * S := by ring
  have hthirdPos : 0 < thetaCuspBornWittenLogThirdDerivative 1 u := by
    linarith
  have hSthird : 2 < S * thetaCuspBornWittenLogThirdDerivative 1 u := by
    have hmul := mul_le_mul_of_nonneg_right hscale hthirdPos.le
    have h36 : (36 : ℝ) < thetaCuspBornWittenLogThirdDerivative 1 u := by
      have : (36 : ℝ) ≤ 6 * S := by linarith
      exact lt_of_le_of_lt this hthird
    linarith
  have hfifth : thetaCuspBornWittenLogFifthDerivative 1 u <
      16 * S ^ 2 * thetaCuspBornWittenLogThirdDerivative 1 u := by
    have h16S : 0 < 16 * S := mul_pos (by norm_num) hS
    have hlarge := mul_lt_mul_of_pos_left hSthird h16S
    apply hfifthUpper.trans
    convert hlarge using 1 <;> ring
  exact ⟨hthird, hfourth, hfifth⟩

theorem thetaCuspC5FirstAtomProjectiveEnergy_pos
    {u : ℝ} (hu : 0 ≤ u) :
    0 < thetaCuspBornWittenLogThirdDerivative 1 u *
          thetaCuspBornWittenLogFourthDerivative 1 u -
        thetaCuspBornWittenLogCurvature 1 u *
          thetaCuspBornWittenLogFifthDerivative 1 u := by
  let q := thetaCuspBornWittenWeight 1 u
  have hq : 0 < q := by
    simpa only [q] using thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hu
  have hcurv : thetaCuspBornWittenLogCurvature 1 u =
      (2 * q + 3) * (2 + 3 / q ^ 2) := by
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hu]
    change 4 * q + 6 + 6 / q + 9 / q ^ 2 =
      (2 * q + 3) * (2 + 3 / q ^ 2)
    field_simp [hq.ne']
    ring
  rw [hcurv]
  unfold thetaCuspBornWittenLogThirdDerivative
    thetaCuspBornWittenLogFourthDerivative
    thetaCuspBornWittenLogFifthDerivative
  change 0 <
    (2 * q + 3) * (4 - 6 / q ^ 2 - 18 / q ^ 3) *
          ((2 * q + 3) * (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4)) -
        ((2 * q + 3) * (2 + 3 / q ^ 2)) *
          ((2 * q + 3) * (16 - 24 / q ^ 2 - 504 / q ^ 3 -
            1944 / q ^ 4 - 1944 / q ^ 5))
  rw [show
    (2 * q + 3) * (4 - 6 / q ^ 2 - 18 / q ^ 3) *
          ((2 * q + 3) * (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4)) -
        ((2 * q + 3) * (2 + 3 / q ^ 2)) *
          ((2 * q + 3) * (16 - 24 / q ^ 2 - 504 / q ^ 3 -
            1944 / q ^ 4 - 1944 / q ^ 5)) =
      (2 * q + 3) ^ 2 *
        (1296 / q ^ 3 + 4536 / q ^ 4 + 4536 / q ^ 5 +
          2916 / q ^ 6 + 2916 / q ^ 7) by
    field_simp [hq.ne']
    ring]
  positivity

def thetaCuspC5FirstFaceSeamObstruction (u : ℝ) : ℝ :=
  let A := thetaCuspBornWittenLogCurvature 1 u
  let p := thetaCuspBornWittenLogThirdDerivative 1 u
  let B := thetaCuspBornWittenLogFourthDerivative 1 u
  let C := thetaCuspBornWittenLogFifthDerivative 1 u
  let F₂ := thetaCuspLikelihoodSourceLogPartitionJetTwo u
  let F₃ := thetaCuspLikelihoodSourceLogPartitionJetThree u
  let F₄ := thetaCuspLikelihoodSourceLogPartitionJetFour u
  let F₅ := thetaCuspLikelihoodSourceLogPartitionJetFive u
  F₂ * (2 * p * B - A * C) -
    A * (-2 * F₃ * B - 2 * p * F₄ + A * F₅ + F₂ * C)

theorem thetaCuspC5FirstFaceSeamObstruction_pos
    {u : ℝ} (hu : 0 ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < thetaCuspC5FirstFaceSeamObstruction u := by
  let S := thetaCuspSingleAtomReflectionScale 1 u
  let A := thetaCuspBornWittenLogCurvature 1 u
  let p := thetaCuspBornWittenLogThirdDerivative 1 u
  let B := thetaCuspBornWittenLogFourthDerivative 1 u
  let C := thetaCuspBornWittenLogFifthDerivative 1 u
  let F₂ := thetaCuspLikelihoodSourceLogPartitionJetTwo u
  let F₃ := thetaCuspLikelihoodSourceLogPartitionJetThree u
  let F₄ := thetaCuspLikelihoodSourceLogPartitionJetFour u
  let F₅ := thetaCuspLikelihoodSourceLogPartitionJetFive u
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) hscale
  have hA : 0 < A := by
    have hfloor := thetaCuspBornWittenLogCurvature_floor
      (n := 1) (by norm_num) hu
    norm_num at hfloor
    change 0 < thetaCuspBornWittenLogCurvature 1 u
    exact (mul_pos (by norm_num) Real.pi_pos).trans_le hfloor
  have hF₂ : 0 < F₂ := by
    simpa only [F₂] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hu
  have hF₃ : F₃ < 0 := by
    simpa only [F₃] using thetaCuspLikelihoodSourceLogPartitionJetThree_neg hu
  have hF₄ : 0 < F₄ := by
    simpa only [F₄] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hu
  have hF₅ : F₅ < 0 := by
    simpa only [F₅] using thetaCuspLikelihoodSourceLogPartitionJetFive_neg hu
  rcases thetaCuspC5FirstFaceAtomBounds hu hscale with ⟨hpLower, hB, hC⟩
  change 6 * S < p at hpLower
  change B < 2 * S * p at hB
  change C < 16 * S ^ 2 * p at hC
  have hp : 0 < p := (mul_pos (by norm_num) hS).trans hpLower
  have hBpos : 0 < B := by
    simpa only [B] using thetaCuspBornWittenLogFourthDerivative_pos
      (n := 1) (by norm_num) hu
  have hcool₂ : 4 * S * F₂ < -F₃ := by
    simpa only [S, F₂, F₃] using
      four_mul_scale_mul_jetTwo_lt_neg_jetThree hu hscale
  have hcool₄ : 4 * S * (-F₃) < F₄ := by
    simpa only [S, F₃, F₄] using
      four_mul_scale_mul_neg_jetThree_lt_jetFour hu hscale
  have hfirst : 2 * (-F₃) * B < p * F₄ := by
    have hmulB := mul_lt_mul_of_pos_left hB (neg_pos.mpr hF₃)
    have hpre : 2 * (-F₃) * B < p * (4 * S * (-F₃)) := by
      calc
        2 * (-F₃) * B = 2 * ((-F₃) * B) := by ring
        _ < 2 * ((-F₃) * (2 * S * p)) :=
          mul_lt_mul_of_pos_left hmulB (by norm_num)
        _ = p * (4 * S * (-F₃)) := by ring
    exact hpre.trans (mul_lt_mul_of_pos_left hcool₄ hp)
  have h16cool : 16 * S ^ 2 * F₂ < F₄ := by
    have hscaleCool := mul_lt_mul_of_pos_left hcool₂
      (mul_pos (show (0 : ℝ) < 4 by norm_num) hS)
    have hstep : 16 * S ^ 2 * F₂ < 4 * S * (-F₃) := by
      calc
        16 * S ^ 2 * F₂ = (4 * S) * (4 * S * F₂) := by ring
        _ < (4 * S) * (-F₃) := hscaleCool
    exact hstep.trans hcool₄
  have hsecond : F₂ * C < p * F₄ := by
    have hmulC := mul_lt_mul_of_pos_left hC hF₂
    have hpre : F₂ * C < p * (16 * S ^ 2 * F₂) := by
      calc
        F₂ * C < F₂ * (16 * S ^ 2 * p) := hmulC
        _ = p * (16 * S ^ 2 * F₂) := by ring
    exact hpre.trans (mul_lt_mul_of_pos_left h16cool hp)
  have hdirection :
      -2 * F₃ * B - 2 * p * F₄ + A * F₅ + F₂ * C < 0 := by
    have hsum : 2 * (-F₃) * B + F₂ * C < 2 * (p * F₄) := by
      simpa only [two_mul] using add_lt_add hfirst hsecond
    have hAF₅ : A * F₅ < 0 := mul_neg_of_pos_of_neg hA hF₅
    nlinarith
  have hprojective := thetaCuspC5FirstAtomProjectiveEnergy_pos hu
  change 0 < p * B - A * C at hprojective
  have hK : 0 < 2 * p * B - A * C := by
    have hpB : 0 < p * B := mul_pos hp hBpos
    linarith
  unfold thetaCuspC5FirstFaceSeamObstruction
  dsimp only
  change 0 < F₂ * (2 * p * B - A * C) -
    A * (-2 * F₃ * B - 2 * p * F₄ + A * F₅ + F₂ * C)
  have hleft := mul_pos hF₂ hK
  have hright := mul_neg_of_pos_of_neg hA hdirection
  linarith

end

end RHTower
