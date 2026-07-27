import GaloisForLFunctions.RHTower.XiSquaredSeamLowDyadicTail
import GaloisForLFunctions.RHTower.XiOrderEighteenCornerSourceExclusion
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

open Complex

namespace RHTower

noncomputable section

theorem orderThirtyTwoReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 417 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 32).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 49 / 1000) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

theorem xiOrderNineteenSectorRatio_unconditional
    (q : XiZeroCopy) {y : ℝ} (hy : 1 / 4 < y) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [hoff]
    norm_num
    have himsq : 0 ≤ (q.1 : ℂ).im ^ 2 := sq_nonneg _
    nlinarith
  · by_contra hnot
    have hcorner := xiOrderNineteenSectorFailure_mem_edgeCorner q hoff hy
      (le_of_not_gt hnot)
    exact not_exists_xiZeroCopy_mem_orderEighteen_edgeCorner ⟨q, hcorner⟩

theorem xiOrderThirtyTwoSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 20 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    417 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 417) (u₀ := 1 / 20)
    (v₀ := 85) (y₀ := 1 / 4) (by norm_num) hy.le hinner
    (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

theorem xiOrderThirtyTwoSectorRatio_of_fourHundredSeventeen_le_im_sq
    (q : XiZeroCopy) (hhigh : 417 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    417 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner_of_lt_width (N := 417)
    (u₀ := 1 / 4) (v₀ := 417) (y₀ := 1 / 4) (by norm_num) hy.le
    (xi_divisor_support_centered_re_sq_lt_quarter q.1) hhigh (by norm_num) (by norm_num)
    (by norm_num)

theorem xiOrderThirtyTwoSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        417 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 20 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 417 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiOrderThirtyTwoSectorRatio_of_offLine_inner q hoff h hy)
    (fun h => xiOrderThirtyTwoSectorRatio_of_fourHundredSeventeen_le_im_sq q h hy) hfail

theorem xiOrderThirtyTwoReciprocalPower_nonpos_mem_annulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 32).re ≤ 0) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    (1 / 20 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 417 ∧
      147 * B ^ 2 < A ^ 2 ∧ A ^ 2 ≤ 417 * B ^ 2 :=
  xiZeroCopy_reciprocalPower_nonpos_of_sector q hy
    (fun _ _ hA h => orderThirtyTwoReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hupper =>
      have hcorner := xiOrderThirtyTwoSectorFailure_mem_edgeCorner q hoff hy hupper
      ⟨hcorner.1, hcorner.2.1, hcorner.2.2.1, hcorner.2.2.2,
        xiOrderNineteenSectorRatio_unconditional q hy, hupper⟩)
    hnonpos

/-- No fixed-shift Xi atom occupies the only angular annulus in which power `32` can fail. -/
def XiSquaredSeamPowerThirtyTwoAnnulusEmpty : Prop :=
  ¬ ∃ q : XiZeroCopy,
    147 * xiSquaredSeamTransverseB q ^ 2 < xiSquaredSeamOneRadialA q ^ 2 ∧
      xiSquaredSeamOneRadialA q ^ 2 ≤ 417 * xiSquaredSeamTransverseB q ^ 2

theorem xiSquaredSeamDyadic_rung_five_pos_of_annulusEmpty
    (h : XiSquaredSeamPowerThirtyTwoAnnulusEmpty) (q : XiZeroCopy) :
    0 < ((xiSquaredSeamOneCoordinate q) ^ (2 ^ 5)).re := by
  norm_num
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hA := xiSquaredSeamOneRadialA_pos q
    apply orderThirtyTwoReciprocalPower_re_pos_of_sectorRatio hA
    simp [xiSquaredSeamTransverseB, hoff]
    exact sq_pos_of_pos hA
  · by_contra hnot
    have hnonpos : ((xiSquaredSeamOneCoordinate q) ^ 32).re ≤ 0 := le_of_not_gt hnot
    have hann := xiOrderThirtyTwoReciprocalPower_nonpos_mem_annulus q hoff
      (y := 1) (by norm_num) (by
        simpa [xiSquaredSeamOneCoordinate, xiSquaredSeamOneRadialA,
          xiSquaredSeamTransverseB] using hnonpos)
    apply h
    refine ⟨q, ?_⟩
    exact ⟨hann.2.2.2.2.1, hann.2.2.2.2.2⟩

/-- Remaining fixed-shift dyadic atom signs beginning at power `64`. -/
def XiSquaredSeamDyadicTailFromSix : Prop :=
  ∀ q : XiZeroCopy, ∀ k : ℕ, 6 ≤ k →
    0 ≤ ((xiSquaredSeamOneCoordinate q) ^ (2 ^ k)).re

theorem xiSquaredSeamDyadicHalfPlane_of_annulusEmpty_of_tailFromSix
    (hann : XiSquaredSeamPowerThirtyTwoAnnulusEmpty)
    (htail : XiSquaredSeamDyadicTailFromSix) : XiSquaredSeamDyadicHalfPlane := by
  intro q k
  by_cases hk : 6 ≤ k
  · exact htail q k hk
  · have hklt : k < 6 := by omega
    interval_cases k
    · exact (xiSquaredSeamDyadic_rung_zero_pos q).le
    · exact (xiSquaredSeamDyadic_rung_one_pos q).le
    · exact (xiSquaredSeamDyadic_rung_two_pos q).le
    · exact (xiSquaredSeamDyadic_rung_three_pos q).le
    · exact (xiSquaredSeamDyadic_rung_four_pos q).le
    · exact (xiSquaredSeamDyadic_rung_five_pos_of_annulusEmpty hann q).le

theorem xiSquaredSeamPowerThirtyTwoAnnulusEmpty_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiSquaredSeamPowerThirtyTwoAnnulusEmpty := by
  rintro ⟨q, hlower, hupper⟩
  have hre := xi_divisor_support_re_eq_half_of_rh hRH q.1
  have hA := xiSquaredSeamOneRadialA_pos q
  have hB : xiSquaredSeamTransverseB q = 0 := by
    simp [xiSquaredSeamTransverseB, hre]
  rw [hB] at hupper
  norm_num at hupper
  nlinarith [sq_pos_of_pos hA]

/-- **Power-32 annulus / tail-from-64 RH law.** -/
theorem xiSquaredSeamPowerThirtyTwoAnnulusEmpty_and_tailFromSix_iff_riemannHypothesis :
    (XiSquaredSeamPowerThirtyTwoAnnulusEmpty ∧ XiSquaredSeamDyadicTailFromSix) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hann, htail⟩
    exact riemannHypothesis_of_xiSquaredSeamDyadicHalfPlane
      (xiSquaredSeamDyadicHalfPlane_of_annulusEmpty_of_tailFromSix hann htail)
  · intro hRH
    refine ⟨xiSquaredSeamPowerThirtyTwoAnnulusEmpty_of_riemannHypothesis hRH, ?_⟩
    intro q k _
    exact xiSquaredSeamDyadicHalfPlane_of_riemannHypothesis hRH q k

end

end RHTower
