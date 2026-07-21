import GaloisForLFunctions.RHTower.XiSquaredSeamLowDyadicTail
import GaloisForLFunctions.RHTower.XiOrderEighteenCornerSourceExclusion

open Complex

namespace RHTower

noncomputable section

theorem orderThirtyTwoReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 417 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 32).re := by
  let mu : ℂ := ((A : ℂ) - B * I)⁻¹
  have hden : 0 < A ^ 2 + B ^ 2 := by nlinarith [sq_nonneg B]
  have hmure : mu.re = A / (A ^ 2 + B ^ 2) := by
    dsimp only [mu]
    rw [Complex.inv_re, Complex.normSq_apply]
    simp
    ring
  have hmuim : mu.im = B / (A ^ 2 + B ^ 2) := by
    dsimp only [mu]
    rw [Complex.inv_im, Complex.normSq_apply]
    simp
    ring
  have hmurepos : 0 < mu.re := by rw [hmure]; positivity
  have htan : Real.tan (Complex.arg mu) = B / A := by
    rw [Complex.tan_arg, hmuim, hmure]
    field_simp
  have hsq : (1000 * B) ^ 2 < (49 * A) ^ 2 := by
    nlinarith [sq_pos_of_pos hA]
  have habsScaled : |1000 * B| < 49 * A := by
    exact abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
  have habsB : |B| < (49 / 1000 : ℝ) * A := by
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  have habsRatio : |B / A| < 49 / 1000 := by
    rw [abs_div, abs_of_pos hA]
    rw [div_lt_iff₀ hA]
    exact habsB
  have hargRange : |Complex.arg mu| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    exact Or.inl hmurepos
  have htanabs : Real.tan |Complex.arg mu| = |B / A| := by
    by_cases harg : 0 ≤ Complex.arg mu
    · rw [abs_of_nonneg harg, htan, abs_of_nonneg]
      rw [← htan]
      exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two harg
        ((le_abs_self _).trans hargRange.le)
    · have hargneg : Complex.arg mu < 0 := lt_of_not_ge harg
      rw [abs_of_neg hargneg, Real.tan_neg, htan, abs_of_neg]
      rw [← htan]
      exact Real.tan_neg_of_neg_of_pi_div_two_lt hargneg (by
        rw [abs_lt] at hargRange
        exact hargRange.1)
  have hargSmall : |Complex.arg mu| < 49 / 1000 := by
    by_cases hargzero : Complex.arg mu = 0
    · simp [hargzero]
    · have hargabspos : 0 < |Complex.arg mu| := abs_pos.mpr hargzero
      have hlt := Real.lt_tan hargabspos hargRange
      rw [htanabs] at hlt
      exact hlt.trans habsRatio
  have hangle : |32 * Complex.arg mu| < Real.pi / 2 := by
    rw [abs_mul]
    norm_num
    nlinarith [Real.pi_gt_d20]
  have hcos : 0 < Real.cos (32 * Complex.arg mu) := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hangle)
  have hmu : mu ≠ 0 := by
    exact inv_ne_zero (by
      intro hz
      have hzre := congrArg Complex.re hz
      simp at hzre
      linarith)
  have hnorm : 0 < ‖mu‖ ^ 32 := pow_pos (norm_pos_iff.mpr hmu) _
  change 0 < (mu ^ 32).re
  rw [← Complex.norm_mul_exp_arg_mul_I mu, mul_pow, ← Complex.exp_nat_mul]
  have hexp :
      ((32 : ℕ) : ℂ) * ((Complex.arg mu : ℂ) * I) =
        ((32 * Complex.arg mu : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexp, mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [← Complex.ofReal_pow]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_pos hnorm hcos

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
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 1 / 20 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 417 * B ^ 2 ≤ (417 / 5 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hheight : (417 / 5 : ℝ) * v < v ^ 2 := by
    nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 417 * B ^ 2 < A ^ 2
  linarith

theorem xiOrderThirtyTwoSectorRatio_of_fourHundredSeventeen_le_im_sq
    (q : XiZeroCopy) (hhigh : 417 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    417 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 417 ≤ v := by simpa only [v] using hhigh
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 417 * B ^ 2 < 417 * v := by
    rw [hB]
    nlinarith
  have hheight : 417 * v ≤ v ^ 2 := by nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 417 * B ^ 2 < A ^ 2
  linarith

theorem xiOrderThirtyTwoSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        417 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 20 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 417 := by
  have hedge : (1 / 20 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    have hsector := xiOrderThirtyTwoSectorRatio_of_offLine_inner q hoff
      (le_of_not_gt h) hy
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 85 < (q.1 : ℂ).im ^ 2 :=
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 417 := by
    by_contra h
    have hsector := xiOrderThirtyTwoSectorRatio_of_fourHundredSeventeen_le_im_sq q
      (le_of_not_gt h) hy
    linarith
  exact ⟨hedge, hu, hvlow, hvhigh⟩

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
      147 * B ^ 2 < A ^ 2 ∧ A ^ 2 ≤ 417 * B ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith
  have hupper : A ^ 2 ≤ 417 * B ^ 2 := by
    by_contra h
    have hsector : 417 * B ^ 2 < A ^ 2 := lt_of_not_ge h
    have hpos := orderThirtyTwoReciprocalPower_re_pos_of_sectorRatio hA hsector
    change ((((A : ℂ) - B * I)⁻¹) ^ 32).re ≤ 0 at hnonpos
    linarith
  have hcorner := xiOrderThirtyTwoSectorFailure_mem_edgeCorner q hoff hy
    (by simpa only [A, B, u, v] using hupper)
  have hlower := xiOrderNineteenSectorRatio_unconditional q hy
  exact ⟨hcorner.1, hcorner.2.1, hcorner.2.2.1, hcorner.2.2.2,
    by simpa only [A, B, u, v] using hlower, hupper⟩

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
