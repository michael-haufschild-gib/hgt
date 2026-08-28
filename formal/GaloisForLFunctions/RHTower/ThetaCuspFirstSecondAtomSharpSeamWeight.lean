import GaloisForLFunctions.RHTower.ThetaCuspFirstSecondAtomCrossHankelObstruction

/-!
# Sharp first--second theta-atom seam weight

The second-to-first theta likelihood ratio at the modular seam has an exact one-exponential
formula.  The corpus exponential enclosure then places this physical weight below `1 / 445`.
Combined with the first--second cross-defect classification, this upgrades diagonal absorption
from qualitative positivity to a uniform signed-second reserve greater than `21`.
-/

namespace RHTower

noncomputable section

/-- Exact closed form for the physical second-to-first theta likelihood ratio at the seam. -/
theorem thetaCuspSecondAtomLikelihoodRatio_seam_eq_exp_neg_three_pi :
    thetaCuspAtomLikelihoodRatio 2 0 =
      ((32 * Real.pi - 12) / (2 * Real.pi - 3)) * Real.exp (-3 * Real.pi) := by
  unfold thetaCuspAtomLikelihoodRatio thetaCuspSourceTerm thetaCuspSeed
  norm_num
  rw [show Real.exp (-(Real.pi * 4)) =
      Real.exp (-3 * Real.pi) * Real.exp (-Real.pi) by
    rw [← Real.exp_add]
    congr 1
    ring]
  field_simp [Real.pi_ne_zero, (Real.exp_pos (-Real.pi)).ne']
  ring

/-- Sharp rational chamber certificate for physical second-atom mixing at the modular seam. -/
theorem fourHundredFortyFive_mul_thetaCuspSecondAtomLikelihoodRatio_seam_lt_one :
    445 * thetaCuspAtomLikelihoodRatio 2 0 < 1 := by
  have hden : 0 < 2 * Real.pi - 3 := by nlinarith [Real.pi_gt_three]
  have he := thetaCusp_exp_neg_three_pi_lt
  rw [thetaCuspSecondAtomLikelihoodRatio_seam_eq_exp_neg_three_pi]
  rw [show 445 * ((32 * Real.pi - 12) / (2 * Real.pi - 3) *
      Real.exp (-3 * Real.pi)) =
      (445 * (32 * Real.pi - 12) * Real.exp (-3 * Real.pi)) /
        (2 * Real.pi - 3) by ring]
  apply (div_lt_iff₀ hden).2
  have hnum : 0 < 32 * Real.pi - 12 := by nlinarith [Real.pi_gt_three]
  have hscale := mul_lt_mul_of_pos_left he
    (mul_pos (by norm_num : (0 : ℝ) < 445) hnum)
  exact hscale.trans (by nlinarith [Real.pi_gt_d20])

/-- Quantitative absorption law: throughout the seam chamber, every nonnegative second-atom
weight below `1 / 445` leaves more than `21` units of normalized signed-second reserve. -/
theorem twentyOne_lt_thetaCuspBornWittenFirstSecondMixedSignedSecondProfile
    {q rho : ℝ} (hqlo : 41 / 25 ≤ q) (hqhi : q ≤ 23 / 14)
    (hrho : 0 ≤ rho) (hrhoSmall : 445 * rho ≤ 1) :
    21 < thetaCuspBornWittenFirstSecondMixedSignedSecondProfile q rho := by
  let r := 4 * q + 9 / 2
  have hq0 : 0 < q := by linarith
  have hcross :=
    neg_oneThousandFiftyEight_lt_thetaCuspBornWittenCrossSignedSecondProfile
      hqlo hqhi
  have hcrossBudget : 0 ≤ rho *
      (thetaCuspBornWittenCrossSignedSecondProfile q (4 * q + 9 / 2) + 1058) := by
    exact mul_nonneg hrho (by linarith)
  have hcurvq : 12 < thetaCuspBornWittenLogCurvatureFactoredProfile q := by
    have hleft : 0 < 2 * q + 3 := by positivity
    have hright : 2 < 2 + 3 / q ^ 2 := by
      have hdiv : 0 < 3 / q ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hq0)
      linarith
    have hmul : (2 * q + 3) * 2 <
        (2 * q + 3) * (2 + 3 / q ^ 2) :=
      mul_lt_mul_of_pos_left hright hleft
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    nlinarith
  have hcurvr : 0 ≤ thetaCuspBornWittenLogCurvatureFactoredProfile r := by
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    positivity
  have hdiag : 0 ≤ 2 * rho ^ 2 *
      thetaCuspBornWittenLogCurvatureFactoredProfile r := by positivity
  unfold thetaCuspBornWittenFirstSecondMixedSignedSecondProfile
  dsimp only [r] at hcurvr hdiag ⊢
  nlinarith

/-- Unconditional physical survivor at the modular seam: first--second diagonal absorption has
normalized signed-second reserve greater than `21`. -/
theorem twentyOne_lt_thetaCuspFirstSecondPhysicalMixedSignedSecond_seam :
    21 < thetaCuspBornWittenFirstSecondMixedSignedSecondProfile
      (thetaCuspBornWittenWeight 1 0) (thetaCuspAtomLikelihoodRatio 2 0) := by
  have hq1 : thetaCuspBornWittenWeight 1 0 = Real.pi - 3 / 2 := by
    simp [thetaCuspBornWittenWeight, thetaCuspMorseSuperpotential,
      thetaCuspMorseScale]
    ring
  apply twentyOne_lt_thetaCuspBornWittenFirstSecondMixedSignedSecondProfile
  · rw [hq1]
    nlinarith [Real.pi_gt_d2]
  · rw [hq1]
    nlinarith [Real.pi_lt_d4]
  · exact thetaCuspSecondAtomLikelihoodRatio_seam_nonneg
  · exact fourHundredFortyFive_mul_thetaCuspSecondAtomLikelihoodRatio_seam_lt_one.le

end

end RHTower
