import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopyLowerTransport
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLikelihoodGain

/-!
# Completed inverse-curvature transport on the structural theta tail

Let `A = -(log Theta)''` be completed theta log curvature. This file proves the new strict
projective inequality

`2 * (A')^2 - A * A'' > 0`

throughout first-atom scale `>= 6`, then converts it into strict increase of `-A' / A^2`.
The source inequality is an exact positive polynomial after clearing the sixth power of the
Born--Witten coordinate. Completion preserves it without a likelihood-jet estimate: the third
jet is shifted upward, while positive second and fourth likelihood jets shrink the adverse
curvature product.

RH chain: completed inverse-curvature transport is the first monotone-ratio premise for the
completed endpoint sign `velocityCenter(1) < 0`; that endpoint closes the zero face of Conjecture
K, hence the shifted Bose cone route to `M''' > 0`, direct-J, rank-four/Ptolemy, CLG/TTF or Weil
positivity, and RH. The remaining endpoint burden is the companion projective comparison.
-/

open Set

namespace RHTower

noncomputable section

private theorem thetaCuspSingleAtomReflectionScale_one_eq_morseScale (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x = thetaCuspMorseScale 1 x := by
  unfold thetaCuspSingleAtomReflectionScale thetaCuspMorseScale
  rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  norm_num
  ring

private theorem nineHalves_le_thetaCuspBornWittenWeight_one_of_six_le_scale
    {x : ℝ} (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (9 / 2 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
  have hs : 6 ≤ thetaCuspMorseScale 1 x := by
    rw [← thetaCuspSingleAtomReflectionScale_one_eq_morseScale]
    exact hscale
  rw [thetaCuspBornWittenWeight_eq]
  linarith

/-- Exact first-atom inverse-curvature energy. The scale-six entrance becomes `q >= 9/2`,
and clearing `q^6` leaves a polynomial positive after translating by `9/2`. -/
theorem thetaCuspBornWittenInverseCurvatureEnergy_pos_of_six_le_scale
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < 2 * thetaCuspBornWittenLogThirdDerivative 1 x ^ 2 -
      thetaCuspBornWittenLogCurvature 1 x *
        thetaCuspBornWittenLogFourthDerivative 1 x := by
  let q := thetaCuspBornWittenWeight 1 x
  have hq : 0 < q := by
    simpa only [q] using thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hq45 : (9 / 2 : ℝ) ≤ q := by
    simpa only [q] using
      nineHalves_le_thetaCuspBornWittenWeight_one_of_six_le_scale hscale
  let y := q - 9 / 2
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hqeq : q = y + 9 / 2 := by dsimp only [y]; ring
  have hpoly : 0 <
      16 * q ^ 6 - 144 * q ^ 4 - 504 * q ^ 3 - 288 * q ^ 2 + 108 * q + 162 := by
    rw [hqeq]
    ring_nf
    positivity
  have hcurv : thetaCuspBornWittenLogCurvature 1 x =
      (2 * q + 3) * (2 + 3 / q ^ 2) := by
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    change 4 * q + 6 + 6 / q + 9 / q ^ 2 =
      (2 * q + 3) * (2 + 3 / q ^ 2)
    field_simp [hq.ne']
    ring
  have hqdef : thetaCuspBornWittenWeight 1 x = q := by rfl
  rw [hcurv]
  dsimp only [thetaCuspBornWittenLogThirdDerivative,
    thetaCuspBornWittenLogFourthDerivative]
  rw [hqdef]
  change 0 < 2 * ((2 * q + 3) * (4 - 6 / q ^ 2 - 18 / q ^ 3)) ^ 2 -
    ((2 * q + 3) * (2 + 3 / q ^ 2)) *
      ((2 * q + 3) * (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4))
  rw [show
      2 * ((2 * q + 3) * (4 - 6 / q ^ 2 - 18 / q ^ 3)) ^ 2 -
          ((2 * q + 3) * (2 + 3 / q ^ 2)) *
            ((2 * q + 3) * (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4)) =
        (2 * q + 3) ^ 2 *
          (16 * q ^ 6 - 144 * q ^ 4 - 504 * q ^ 3 - 288 * q ^ 2 +
            108 * q + 162) / q ^ 6 by
      field_simp [hq.ne']
      ring]
  exact div_pos (mul_pos (sq_pos_of_pos (by linarith)) hpoly) (pow_pos hq 6)

theorem thetaCuspBornWittenLogThirdDerivative_pos_of_six_le_scale
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspBornWittenLogThirdDerivative 1 x := by
  let q := thetaCuspBornWittenWeight 1 x
  have hq : 0 < q := by
    simpa only [q] using thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hq45 : (9 / 2 : ℝ) ≤ q := by
    simpa only [q] using
      nineHalves_le_thetaCuspBornWittenWeight_one_of_six_le_scale hscale
  let y := q - 9 / 2
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hqeq : q = y + 9 / 2 := by dsimp only [y]; ring
  have hpoly : 0 < 4 * q ^ 3 - 6 * q - 18 := by
    rw [hqeq]
    ring_nf
    positivity
  have hinner : 0 < 4 - 6 / q ^ 2 - 18 / q ^ 3 := by
    rw [show 4 - 6 / q ^ 2 - 18 / q ^ 3 =
        (4 * q ^ 3 - 6 * q - 18) / q ^ 3 by
      field_simp [hq.ne']]
    exact div_pos hpoly (pow_pos hq 3)
  dsimp only [thetaCuspBornWittenLogThirdDerivative]
  rw [show thetaCuspBornWittenWeight 1 x = q by rfl]
  exact mul_pos (by linarith) hinner

/-- Completion-stability theorem. No fourth-jet likelihood bound is used. If completed fourth
curvature is nonpositive the result is immediate; otherwise completion strictly shrinks both
positive factors in `A * A''` and strictly enlarges `(A')^2`. -/
theorem thetaCuspCompletedInverseCurvatureEnergy_pos_of_six_le_scale
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 <
      2 * (thetaCuspBornWittenLogThirdDerivative 1 x -
          thetaCuspLikelihoodSourceLogPartitionJetThree x) ^ 2 -
        thetaCuspFullReflectedLogCurvature x *
          thetaCuspFullReflectedLogFourthJet x := by
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let p0 := thetaCuspBornWittenLogThirdDerivative 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  let F2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let F3 := thetaCuspLikelihoodSourceLogPartitionJetThree x
  let F4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  have hA0floor : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hx
  have hA0 : 0 < A0 := by linarith
  have hp0 : 0 < p0 := by
    simpa only [p0] using
      thetaCuspBornWittenLogThirdDerivative_pos_of_six_le_scale hx hscale
  have hF2pos : 0 < F2 := by
    simpa only [F2] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hF2le : F2 ≤ 13 / 10 := by
    simpa only [F2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have hF3neg : F3 < 0 := by
    simpa only [F3] using thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx
  have hF4pos : 0 < F4 := by
    simpa only [F4] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have hA : 0 < A0 - F2 := by linarith
  have hp : 0 < p0 - F3 := by linarith
  have hA_lt : A0 - F2 < A0 := by linarith
  have hB_lt : B0 - F4 < B0 := by linarith
  have hborn : 0 < 2 * p0 ^ 2 - A0 * B0 := by
    simpa only [A0, p0, B0] using
      thetaCuspBornWittenInverseCurvatureEnergy_pos_of_six_le_scale hx hscale
  rw [show thetaCuspBornWittenLogThirdDerivative 1 x = p0 by rfl,
    show thetaCuspLikelihoodSourceLogPartitionJetThree x = F3 by rfl]
  change 0 < 2 * (p0 - F3) ^ 2 - (A0 - F2) * (B0 - F4)
  by_cases hB : B0 - F4 ≤ 0
  · have hAB : (A0 - F2) * (B0 - F4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA.le hB
    nlinarith [sq_pos_of_pos hp]
  · have hBpos : 0 < B0 - F4 := lt_of_not_ge hB
    have hleft : (A0 - F2) * (B0 - F4) < A0 * (B0 - F4) :=
      mul_lt_mul_of_pos_right hA_lt hBpos
    have hright : A0 * (B0 - F4) < A0 * B0 :=
      mul_lt_mul_of_pos_left hB_lt hA0
    have hsq : p0 ^ 2 < (p0 - F3) ^ 2 := by nlinarith
    nlinarith

private theorem thetaCuspLogCurvature_eq_fullReflected
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvature x = thetaCuspFullReflectedLogCurvature x := by
  unfold thetaCuspLogCurvature thetaCuspFullReflectedLogCurvature
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx]
  ring

private theorem thetaCuspLogCurvatureJet_eq_fullReflected
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvatureJet x =
      thetaCuspBornWittenLogThirdDerivative 1 x -
        thetaCuspLikelihoodSourceLogPartitionJetThree x := by
  unfold thetaCuspLogCurvatureJet
  rw [iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx,
    ← thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx]
  unfold thetaCuspFirstAtomLogJetThree
  ring

private theorem thetaCuspLogCurvatureJetTwo_eq_fullReflected
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvatureJetTwo x = thetaCuspFullReflectedLogFourthJet x := by
  unfold thetaCuspLogCurvatureJetTwo thetaCuspFullReflectedLogFourthJet
  rw [iteratedDeriv_four_thetaCuspLogSource_eq_factor hx,
    ← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx]
  ring

/-- Native completed-source form of inverse-curvature energy positivity. -/
theorem thetaCuspIntrinsicCompletedInverseCurvatureEnergy_pos_of_six_le_scale
    {x : ℝ} (hx : 0 < x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < 2 * thetaCuspLogCurvatureJet x ^ 2 -
      thetaCuspLogCurvature x * thetaCuspLogCurvatureJetTwo x := by
  rw [thetaCuspLogCurvature_eq_fullReflected hx,
    thetaCuspLogCurvatureJet_eq_fullReflected hx,
    thetaCuspLogCurvatureJetTwo_eq_fullReflected hx]
  exact thetaCuspCompletedInverseCurvatureEnergy_pos_of_six_le_scale hx.le hscale

/-- Derivative of reciprocal completed curvature. -/
def thetaCuspCompletedInverseCurvatureSlope (x : ℝ) : ℝ :=
  -thetaCuspLogCurvatureJet x / thetaCuspLogCurvature x ^ 2

theorem hasDerivAt_thetaCuspCompletedInverseCurvatureSlope (x : ℝ) :
    HasDerivAt thetaCuspCompletedInverseCurvatureSlope
      ((2 * thetaCuspLogCurvatureJet x ^ 2 -
          thetaCuspLogCurvature x * thetaCuspLogCurvatureJetTwo x) /
        thetaCuspLogCurvature x ^ 3) x := by
  have hA := hasDerivAt_thetaCuspLogCurvature x
  have hp := hasDerivAt_thetaCuspLogCurvatureJet x
  have hApos := thetaCuspLogCurvature_pos x
  have hquot := hp.neg.div (hA.pow 2) (pow_ne_zero 2 hApos.ne')
  change HasDerivAt
    (fun y => -thetaCuspLogCurvatureJet y / thetaCuspLogCurvature y ^ 2) _ x
  refine hquot.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.neg_apply]
  field_simp [hApos.ne']
  ring

private theorem thetaCuspSingleAtomReflectionScale_one_mono
    {x y : ℝ} (hxy : x ≤ y) :
    thetaCuspSingleAtomReflectionScale 1 x ≤
      thetaCuspSingleAtomReflectionScale 1 y := by
  unfold thetaCuspSingleAtomReflectionScale
  norm_num
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le

/-- Completed inverse-curvature slope is strictly increasing on every structural tail. This is
the monotone-ratio transport statement consumed by the completed endpoint problem. -/
theorem strictMonoOn_thetaCuspCompletedInverseCurvatureSlope_of_scale
    {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hscale₀ : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x₀) :
    StrictMonoOn thetaCuspCompletedInverseCurvatureSlope (Set.Ici x₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
  · intro x hx
    exact (hasDerivAt_thetaCuspCompletedInverseCurvatureSlope x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hxpos : 0 < x := hx₀.trans hx
    rw [(hasDerivAt_thetaCuspCompletedInverseCurvatureSlope x).deriv]
    exact div_pos
      (thetaCuspIntrinsicCompletedInverseCurvatureEnergy_pos_of_six_le_scale hxpos
        (hscale₀.trans (thetaCuspSingleAtomReflectionScale_one_mono hx.le)))
      (pow_pos (thetaCuspLogCurvature_pos x) 3)

end

end RHTower
