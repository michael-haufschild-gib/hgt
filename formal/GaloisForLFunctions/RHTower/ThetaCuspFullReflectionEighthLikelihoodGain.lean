import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthLogPositivity
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthBellTransfer
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthGlobal

/-!
# Quantitative eighth-likelihood gain in full reflected curvature

The complete fourth reflected jet makes the eighth-likelihood coefficient
strictly favorable.  Exact Bell algebra then converts the quantitative literal
logarithmic eighth-jet floor into an explicit positive contribution to native
rank-three reflected curvature.
-/

namespace RHTower

noncomputable section

/-- Rank-three curvature with lower complete-source jets retained exactly, but before the
favorable eighth likelihood correction is inserted. -/
def thetaCuspFullReflectionEighthBornTopBaseline (x : ℝ) : ℝ :=
  let A := thetaCuspFullReflectedLogCurvature x
  let B := thetaCuspFullReflectedLogFourthJet x
  let C := thetaCuspFullReflectedLogSixthJet x
  let D0 := thetaCuspBornWittenLogEighthDerivative 1 x
  768 * A ^ 6 - 1344 * A ^ 4 * B + 304 * A ^ 2 * B ^ 2 -
    68 * B ^ 3 + 128 * A ^ 3 * C - 4 * A ^ 2 * D0 + B * D0 - C ^ 2

/-- Complete fourth reflected log jet is below twice the square of complete curvature. -/
theorem thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullReflectedLogFourthJet x <
      2 * thetaCuspFullReflectedLogCurvature x ^ 2 := by
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let A := A0 - e2
  let B := B0 - e4
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using
      nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx
  have he2pos : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have he2upper : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have he4pos : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ 2 := by
    simpa only [A0, B0] using
      thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
        (n := 1) (by norm_num) hx
  have hAwA : A0 - 13 / 10 ≤ A := by dsimp only [A]; linarith
  have hratio : (177 / 190 : ℝ) * A0 ≤ A0 - 13 / 10 := by
    nlinarith
  have hratioA : (177 / 190 : ℝ) * A0 ≤ A := hratio.trans hAwA
  have hratio0 : 0 ≤ (177 / 190 : ℝ) * A0 := by positivity
  have hratioSq : (177 / 190 : ℝ) ^ 2 * A0 ^ 2 ≤ A ^ 2 := by
    have hpow := pow_le_pow_left₀ hratio0 hratioA 2
    simpa only [mul_pow] using hpow
  have hBlt : B < B0 := by dsimp only [B]; linarith
  have hB0two : B0 < 2 * A ^ 2 := by
    have hcoef : (6 / 5 : ℝ) < 2 * (177 / 190 : ℝ) ^ 2 := by norm_num
    have hA0sq : 0 < A0 ^ 2 := by positivity
    nlinarith [mul_pos (sub_pos.mpr hcoef) hA0sq]
  change B < 2 * A ^ 2
  linarith

/-- Exact algebraic gain: eighth likelihood positivity enters D1 with coefficient `4A²-B`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_eq_baseline_add_likelihoodGain
    (x : ℝ) :
    thetaCuspFullReflectionEighthHankelCurvature x =
      thetaCuspFullReflectionEighthBornTopBaseline x +
        (4 * thetaCuspFullReflectedLogCurvature x ^ 2 -
          thetaCuspFullReflectedLogFourthJet x) *
            thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  unfold thetaCuspFullReflectionEighthHankelCurvature
    thetaCuspFullReflectionEighthBornTopBaseline
    thetaCuspFullReflectedLogEighthJet
  ring

/-- The literal eighth likelihood channel contributes a strict, explicit D1-scale gain. -/
theorem thetaCuspFullReflectionEighthBornTopBaseline_add_quantitativeGain_lt
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullReflectionEighthBornTopBaseline x +
        128000 * thetaCuspFullReflectedLogCurvature x ^ 2 *
          thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
          Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspFullReflectionEighthHankelCurvature x := by
  let A := thetaCuspFullReflectedLogCurvature x
  let B := thetaCuspFullReflectedLogFourthJet x
  let S := thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
    Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x))
  let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
  have hA0 : 0 < A := by
    let A0 := thetaCuspBornWittenLogCurvature 1 x
    let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
    have hfirst : (19 : ℝ) ≤ A0 := by
      simpa only [A0] using
        nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx
    have he2 : e2 ≤ (13 / 10 : ℝ) := by
      simpa only [e2] using
        thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
    dsimp only [A, thetaCuspFullReflectedLogCurvature, A0, e2]
    linarith
  have hcoef : 2 * A ^ 2 < 4 * A ^ 2 - B := by
    have hB := thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq hx
    simpa only [A, B] using (show
      2 * thetaCuspFullReflectedLogCurvature x ^ 2 <
        4 * thetaCuspFullReflectedLogCurvature x ^ 2 -
          thetaCuspFullReflectedLogFourthJet x by linarith)
  have hcoef0 : 0 < 4 * A ^ 2 - B := lt_trans (by positivity) hcoef
  have hS : 0 < S := by
    dsimp only [S]
    have hscale : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    positivity
  have he8 : 64000 * S < e8 := by
    simpa only [S, e8, mul_assoc] using
      sixtyFourThousand_mul_pow_eight_exp_lt_thetaCuspLikelihoodSourceLogPartitionJetEight hx
  have hgain : 128000 * A ^ 2 * S < (4 * A ^ 2 - B) * e8 := by
    calc
      128000 * A ^ 2 * S = (2 * A ^ 2) * (64000 * S) := by ring
      _ < (4 * A ^ 2 - B) * (64000 * S) :=
        mul_lt_mul_of_pos_right hcoef (by positivity)
      _ < (4 * A ^ 2 - B) * e8 := mul_lt_mul_of_pos_left he8 hcoef0
  rw [thetaCuspFullReflectionEighthHankelCurvature_eq_baseline_add_likelihoodGain]
  simpa only [A, B, S, e8, mul_assoc, add_comm] using add_lt_add_left hgain
    (thetaCuspFullReflectionEighthBornTopBaseline x)

end

end RHTower

