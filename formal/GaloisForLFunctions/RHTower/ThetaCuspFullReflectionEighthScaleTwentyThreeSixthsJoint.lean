import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthCompactLowerBound
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleTwentyThreeSixthsBound
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthSixthSpectralReserve
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthScaleThirtyOneEighths

/-!
# Joint fourth/sixth compact chamber for eighth reflected curvature

Separate source estimates `e₄ > 28` and `e₆ < 14200` are coupled through the exact sixth-spectral
reserve.  Its fourth direction is increasing, while its sixth direction is controlled by a compact
coefficient certificate on `7/3 ≤ q ≤ 19/8`.  The resulting chamber joins the existing large-weight
proof and yields native D1 positivity for every source `x ≥ 1/10`.
-/

namespace RHTower
noncomputable section

def thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
    (q e4 e6 : ℝ) : ℝ :=
  thetaCuspFirstAtomEighthNoSixthLossBaseline q +
    e4 * (68 * e4 ^ 2 +
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 -
        204 * thetaCuspFirstAtomFourthProfile q) * e4 +
      thetaCuspFullReflectionEighthCompactFourthCoefficient q) +
    e6 * ((thetaCuspFullReflectionEighthCompactEighthCoefficient q + e4) *
      (1 / 69) * (q + 3 / 2) ^ 2 -
      (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6))

theorem thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_pos_at_baseline
    {q : ℝ} (hq : (7 / 3 : ℝ) ≤ q) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 14200 := by
  have hqpos : 0 < q := by linarith
  let y := q - 7 / 3
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 16 *
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 14200 := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 7 / 3 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

theorem thetaCuspFirstAtomEighthScaleTwentyThreeSixths_fourthLinearCoefficient_pos
    {q : ℝ} (hq : (7 / 3 : ℝ) ≤ q) :
    0 < 304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 -
      204 * thetaCuspFirstAtomFourthProfile q := by
  have hqpos : 0 < q := by linarith
  let y := q - 7 / 3
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 8 *
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 -
        204 * thetaCuspFirstAtomFourthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile]
    field_simp [hqpos.ne']
    rw [show q = 7 / 3 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 8]

theorem thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_mono_fourth
    {q e4 e6 : ℝ} (hq : (7 / 3 : ℝ) ≤ q)
    (he4 : 28 ≤ e4) (he6zero : 0 ≤ e6) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 e6 ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  have hqpos : 0 < q := by linarith
  let y := q - 7 / 3
  let a := e4 - 28
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  have hmul : 0 ≤ q ^ 16 *
      (thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 -
        thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 e6) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 7 / 3 + y by dsimp only [y]; ring,
      show e4 = 28 + a by dsimp only [a]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

theorem thetaCuspFirstAtomEighthScaleTwentyThreeSixths_sixthLossCoefficient_pos
    {q : ℝ} (hq : (7 / 3 : ℝ) ≤ q) (hqhi : q ≤ 19 / 8) :
    0 < thetaCuspFullReflectionEighthCompactSixthCoefficient q + 14200 -
      (thetaCuspFullReflectionEighthCompactEighthCoefficient q + 28) *
        (1 / 69) * (q + 3 / 2) ^ 2 := by
  have hqpos : 0 < q := by linarith
  let y := q - 7 / 3
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 24 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 12 *
      (thetaCuspFullReflectionEighthCompactSixthCoefficient q + 14200 -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q + 28) *
          (1 / 69) * (q + 3 / 2) ^ 2) := by
    dsimp [thetaCuspFullReflectionEighthCompactSixthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 7 / 3 + y by dsimp only [y]; ring]
    ring_nf
    have hc : 0 < (675038720 / 3 : ℝ) - 25600 * y := by linarith
    have hlast : 0 ≤ y ^ 15 * (675038720 / 3 : ℝ) - y ^ 16 * 25600 := by
      calc
        y ^ 15 * (675038720 / 3 : ℝ) - y ^ 16 * 25600 =
            y ^ 15 * ((675038720 / 3 : ℝ) - 25600 * y) := by ring
        _ ≥ 0 := mul_nonneg (pow_nonneg hy 15) hc.le
    have hprefix : 0 <
        29350567649555002870964 / 43046721 +
          y * (52943049380059878205376 / 14348907) +
          y ^ 2 * (14883535568172176988824 / 1594323) +
          y ^ 3 * (23371735183691135757712 / 1594323) +
          y ^ 4 * (8496477413950713237316 / 531441) +
          y ^ 5 * (757829570301931562288 / 59049) +
          y ^ 6 * (462751137647108238656 / 59049) +
          y ^ 7 * (72978020819098701152 / 19683) +
          y ^ 8 * (999109329374134588 / 729) +
          y ^ 9 * (865681517156012576 / 2187) +
          y ^ 10 * (64582147048462856 / 729) +
          y ^ 11 * (1221941365393328 / 81) +
          y ^ 12 * (153206590177708 / 81) +
          y ^ 13 * (4448567540368 / 27) +
          y ^ 14 * (26727872528 / 3) := by
      positivity
    linarith
  nlinarith [pow_pos hqpos 12]

theorem thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_mono_sixth
    {q e6 : ℝ} (hq : (7 / 3 : ℝ) ≤ q) (hqhi : q ≤ 19 / 8)
    (he6zero : 0 ≤ e6) (he6hi : e6 ≤ 14200) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 14200 ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 e6 := by
  have hcoeff :=
    thetaCuspFirstAtomEighthScaleTwentyThreeSixths_sixthLossCoefficient_pos hq hqhi
  have hgap : 0 ≤ (14200 : ℝ) - e6 := by linarith
  have hfactor : 0 ≤
      thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + 14200 -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q + 28) *
          (1 / 69) * (q + 3 / 2) ^ 2 := by
    linarith
  have hprod := mul_nonneg hgap hfactor
  have hid :
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 e6 -
          thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q 28 14200 =
        (14200 - e6) *
          (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + 14200 -
            (thetaCuspFullReflectionEighthCompactEighthCoefficient q + 28) *
              (1 / 69) * (q + 3 / 2) ^ 2) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve]
    ring
  linarith

theorem thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_pos
    {q e4 e6 : ℝ} (hq : (7 / 3 : ℝ) ≤ q) (hqhi : q ≤ 19 / 8)
    (he4 : 28 ≤ e4) (he6zero : 0 ≤ e6) (he6hi : e6 ≤ 14200) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  have hbase :=
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_pos_at_baseline hq
  have hsix :=
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_mono_sixth
      hq hqhi he6zero he6hi
  have hfourth :=
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_mono_fourth
      hq he4 he6zero
  linarith

/-- The joint fourth/sixth reserve is positive on the compact scale band. -/
theorem thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_scale_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (23 / 6 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (31 / 8 : ℝ)) :
    0 < thetaCuspFullReflectionEighthSixthSpectralReserve x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  have hAq : A = q + 3 / 2 := by
    dsimp only [A, q, thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hqlo : (7 / 3 : ℝ) ≤ q := by
    have hAlow : (23 / 6 : ℝ) ≤ A := by simpa only [A] using hAlo
    rw [hAq] at hAlow
    linarith
  have hqhi : q ≤ (19 / 8 : ℝ) := by
    have hAhigh : A ≤ (31 / 8 : ℝ) := by simpa only [A] using hAhi
    rw [hAq] at hAhigh
    linarith
  have he4 : 28 ≤ e4 := by
    have h := twentyEight_lt_thetaCuspLikelihoodSourceLogPartitionJetFour_of_scale_mem
      hx hAlo hAhi
    simpa only [e4] using h.le
  have he6zero : 0 ≤ e6 := by
    simpa only [e6] using (thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx).le
  have he6hi : e6 ≤ 14200 := by
    have h :=
      thetaCuspLikelihoodSourceLogPartitionJetSix_lt_fourteenThousandTwoHundred_of_twentyThreeSixths_le_scale
        hx hAlo
    simpa only [e6] using h.le
  have hjoint :=
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve_pos
      hqlo hqhi he4 he6zero he6hi
  dsimp only [thetaCuspFullReflectionEighthSixthSpectralReserve]
  dsimp only [q, A, e4, e6] at hjoint ⊢
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    simpa only [A, q] using hAq
  rw [hscale]
  exact hjoint

/-- Native D1 is strict whenever first-atom weight is at least `7/3`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_sevenThirds_le_weight_of_jointReserve
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (7 / 3 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqhi : thetaCuspBornWittenWeight 1 x ≤ (19 / 8 : ℝ)
  · have hscale : thetaCuspSingleAtomReflectionScale 1 x =
        thetaCuspBornWittenWeight 1 x + 3 / 2 := by
      dsimp only [thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
    have hAlo : (23 / 6 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      rw [hscale]
      linarith
    have hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (31 / 8 : ℝ) := by
      rw [hscale]
      linarith
    exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_sixthSpectralReserve_pos hx
      (thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_scale_mem hx hAlo hAhi)
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineteenEighths_le_weight
      hx (le_of_not_ge hqhi)

/-- Exact Taylor certificate placing `x = 1/10` above scale `23/6`. -/
theorem twentyThreeSixths_lt_pi_mul_exp_oneFifth :
    (23 / 6 : ℝ) < Real.pi * Real.exp (1 / 5 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 1 / 5) 8
  have hp := Real.pi_gt_d20
  calc
    (23 / 6 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (∑ k ∈ Finset.range 8, (1 / 5 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.pi * Real.exp (1 / 5 : ℝ) := by gcongr

/-- Native D1 is strict on the complete source half-line `x ≥ 1/10`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_oneTenth_le
    {x : ℝ} (hx : (1 / 10 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (1 / 5 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (23 / 6 : ℝ) < Real.pi * Real.exp (2 * x) :=
    twentyThreeSixths_lt_pi_mul_exp_oneFifth.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (7 / 3 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_sevenThirds_le_weight_of_jointReserve
    hx0 hqBound

end
end RHTower
