import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthScaleEightyNineTwentyFourthsAffineLower
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleEightyNineTwentyFourthsAffineBound
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthScaleOneHundredSeventyNineFortyEighthsAffineJoint

/-!
# Affine fourth/sixth joint chamber at scale 89/24

The moving bounds `372 - 144q < J₄` and `J₆ < (1656/25)(666 - 192q)` are
inserted into exact sixth-spectral eighth-reflection reserve. On
`53/24 ≤ q ≤ 107/48`, baseline and monotonicity certificates are positive.
Native D1 consequently holds for `x ≥ 83/1000`.
-/

namespace RHTower

noncomputable section

/-- Exact moving fourth/sixth baseline leaves strict reserve throughout new chamber. -/
theorem thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_pos_at_baseline
    {q : ℝ} (hqlo : (53 / 24 : ℝ) ≤ q) (hqhi : q ≤ 107 / 48) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
      q (372 - 144 * q) ((1656 / 25 : ℝ) * (666 - 192 * q)) := by
  have hqpos : 0 < q := by linarith
  let y := q - 53 / 24
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) *
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (372 - 144 * q) ((1656 / 25 : ℝ) * (666 - 192 * q)) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 53 / 24 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- Joint reserve is increasing above moving fourth-jet floor. -/
theorem thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_mono_fourth
    {q e4 e6 : ℝ} (hqlo : (53 / 24 : ℝ) ≤ q) (hqhi : q ≤ 107 / 48)
    (he4 : 372 - 144 * q ≤ e4) (he6zero : 0 ≤ e6) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (372 - 144 * q) e6 ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  have hqpos : 0 < q := by linarith
  let y := q - 53 / 24
  let a := e4 - (372 - 144 * q)
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  have hmul : 0 ≤ q ^ (16 : ℕ) *
      (thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 -
        thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
          q (372 - 144 * q) e6) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 53 / 24 + y by dsimp only [y]; ring,
      show e4 = 54 - 144 * y + a by dsimp only [a, y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- Factored sixth-loss coefficient remains positive along moving baseline. -/
theorem thetaCuspFirstAtomEighthScale89Over24Affine_sixthLossCoefficient_pos
    {q : ℝ} (hqlo : (53 / 24 : ℝ) ≤ q) (hqhi : q ≤ 107 / 48) :
    0 < thetaCuspFullReflectionEighthCompactSixthCoefficient q +
        (1656 / 25 : ℝ) * (666 - 192 * q) -
      (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
          (372 - 144 * q)) * (1 / 69) * (q + 3 / 2) ^ (2 : ℕ) := by
  have hqpos : 0 < q := by linarith
  let y := q - 53 / 24
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 48 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (12 : ℕ) *
      (thetaCuspFullReflectionEighthCompactSixthCoefficient q +
          (1656 / 25 : ℝ) * (666 - 192 * q) -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
            (372 - 144 * q)) * (1 / 69) * (q + 3 / 2) ^ (2 : ℕ)) := by
    dsimp [thetaCuspFullReflectionEighthCompactSixthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 53 / 24 + y by dsimp only [y]; ring]
    ring_nf
    have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
    have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
    have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
    have hy5 : 0 ≤ y ^ (5 : ℕ) := by positivity
    have hy6 : 0 ≤ y ^ (6 : ℕ) := by positivity
    have hy7 : 0 ≤ y ^ (7 : ℕ) := by positivity
    have hy8 : 0 ≤ y ^ (8 : ℕ) := by positivity
    have hy9 : 0 ≤ y ^ (9 : ℕ) := by positivity
    have hy10 : 0 ≤ y ^ (10 : ℕ) := by positivity
    have hy11 : 0 ≤ y ^ (11 : ℕ) := by positivity
    have hy12 : 0 ≤ y ^ (12 : ℕ) := by positivity
    have hy13 : 0 ≤ y ^ (13 : ℕ) := by positivity
    have hy14 : 0 ≤ y ^ (14 : ℕ) := by positivity
    have hpair : 0 ≤ y ^ (15 : ℕ) * (16876928000 / 3 : ℝ) - y ^ (16 : ℕ) * 640000 := by
      have hc : 0 ≤ (16876928000 / 3 : ℝ) - 640000 * y := by linarith
      rw [show y ^ (15 : ℕ) * (16876928000 / 3 : ℝ) - y ^ (16 : ℕ) * 640000 =
          y ^ (15 : ℕ) * (16876928000 / 3 - 640000 * y) by ring]
      positivity
    nlinarith
  nlinarith [pow_pos hqpos 12]

/-- Reserve decreases toward moving sixth-jet ceiling. -/
theorem thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_mono_sixth
    {q e6 : ℝ} (hqlo : (53 / 24 : ℝ) ≤ q) (hqhi : q ≤ 107 / 48)
    (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (1656 / 25 : ℝ) * (666 - 192 * q)) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (372 - 144 * q) ((1656 / 25 : ℝ) * (666 - 192 * q)) ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (372 - 144 * q) e6 := by
  let M := (1656 / 25 : ℝ) * (666 - 192 * q)
  let L := 372 - 144 * q
  have hcoeff := thetaCuspFirstAtomEighthScale89Over24Affine_sixthLossCoefficient_pos
    hqlo hqhi
  have hgap : 0 ≤ M - e6 := by dsimp only [M]; linarith
  have hfactor : 0 ≤
      thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q + L) *
          (1 / 69) * (q + 3 / 2) ^ (2 : ℕ) := by
    dsimp only [M, L] at hcoeff ⊢
    linarith
  have hprod := mul_nonneg hgap hfactor
  have hid :
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q L e6 -
          thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q L M =
        (M - e6) *
          (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M -
            (thetaCuspFullReflectionEighthCompactEighthCoefficient q + L) *
              (1 / 69) * (q + 3 / 2) ^ (2 : ℕ)) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve]
    ring
  dsimp only [L, M] at hprod hid ⊢
  linarith

/-- Exact joint chamber for arbitrary physical fourth and sixth jets. -/
theorem thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_pos
    {q e4 e6 : ℝ} (hqlo : (53 / 24 : ℝ) ≤ q) (hqhi : q ≤ 107 / 48)
    (he4 : 372 - 144 * q ≤ e4) (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (1656 / 25 : ℝ) * (666 - 192 * q)) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  have hbase := thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_pos_at_baseline
    hqlo hqhi
  have hsix := thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_mono_sixth
    hqlo hqhi he6zero he6hi
  have hfourth := thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_mono_fourth
    hqlo hqhi he4 he6zero
  linarith

/-- Physical sixth-spectral reserve is positive on `89/24 ≤ A ≤ 179/48`. -/
theorem thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_scale89Over24_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (89 / 24 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 179 / 48) :
    0 < thetaCuspFullReflectionEighthSixthSpectralReserve x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  have hAq : A = q + 3 / 2 := by
    dsimp only [A, q, thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hqlo : (53 / 24 : ℝ) ≤ q := by
    have h := hAlo
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have hqhi : q ≤ (107 / 48 : ℝ) := by
    have h := hAhi
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have he4 : 372 - 144 * q ≤ e4 := by
    have h := fourth89Over24AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
      hx hAlo hAhi
    simpa only [q, e4] using h.le
  have he6zero : 0 ≤ e6 := by
    simpa only [e6] using (thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx).le
  have he6hi : e6 ≤ (1656 / 25 : ℝ) * (666 - 192 * q) := by
    have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale89Over24_affine_weight
      hx hAlo hAhi
    simpa only [q, e6] using h.le
  have hjoint := thetaCuspFirstAtomEighthScale89Over24AffineJointReserve_pos
    hqlo hqhi he4 he6zero he6hi
  dsimp only [thetaCuspFullReflectionEighthSixthSpectralReserve]
  dsimp only [q, A, e4, e6] at hjoint ⊢
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    simpa only [A, q] using hAq
  rw [hscale]
  exact hjoint

/-- Native D1 is strict whenever first-atom weight is at least `53/24`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_53Over24_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (53 / 24 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqhi : thetaCuspBornWittenWeight 1 x ≤ (107 / 48 : ℝ)
  · have hscale : thetaCuspSingleAtomReflectionScale 1 x =
        thetaCuspBornWittenWeight 1 x + 3 / 2 := by
      dsimp only [thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
    have hAlo : (89 / 24 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      rw [hscale]
      linarith
    have hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (179 / 48 : ℝ) := by
      rw [hscale]
      linarith
    exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_sixthSpectralReserve_pos hx
      (thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_scale89Over24_mem
        hx hAlo hAhi)
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_107Over48_le_weight
      hx (le_of_not_ge hqhi)

/-- Exact Taylor certificate placing `x = 83/1000` above scale `89/24`. -/
theorem eightyNineTwentyFourths_lt_pi_mul_exp_eightyThreeFiveHundredths :
    (89 / 24 : ℝ) < Real.pi * Real.exp (83 / 500 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 83 / 500) 8
  have hp := Real.pi_gt_d20
  calc
    (89 / 24 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (∑ k ∈ Finset.range 8, (83 / 500 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.pi * Real.exp (83 / 500 : ℝ) := by gcongr

/-- Native D1 is strict on improved source half-line `x ≥ 83/1000`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_eightyThreeThousandths_le
    {x : ℝ} (hx : (83 / 1000 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (83 / 500 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (89 / 24 : ℝ) < Real.pi * Real.exp (2 * x) :=
    eightyNineTwentyFourths_lt_pi_mul_exp_eightyThreeFiveHundredths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (53 / 24 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_53Over24_le_weight
    hx0 hqBound

end
end RHTower
