import GaloisForLFunctions.RHTower.WeilWorkPBAPJointWidthSector

/-!
# Quantitative seed pole bounds from the actual correlation

The integral of the correlation is the squared source integral. A nonnegative
real correlation supported in a width-W interval therefore places the full
two-pole value between twice that square and its cosh(W/2) multiple.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The zero Fourier value pays the entire correlation integral exactly. -/
theorem joint_integral_real_autocorr (f : JointSmoothTest) :
    (∫ u : ℝ, (EF.weilTest f.1.1 f.1.1 u).re) = ‖∫ u : ℝ, f.1.1 u‖^2 := by
  have hk := WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2
  have hi : Integrable (EF.weilTest f.1.1 f.1.1) :=
    hk.cont.integrable_of_hasCompactSupport hk.supp
  have h := paperFT_weilTest_self_ofReal f.2.continuous f.1.2.2 (0:ℝ)
  have hf0 : paperFT f.1.1 0 = ∫ u : ℝ, f.1.1 u := by simp [paperFT_def]
  have hk0 : paperFT (EF.weilTest f.1.1 f.1.1) 0 =
      ∫ u : ℝ, EF.weilTest f.1.1 f.1.1 u := by simp [paperFT_def]
  simp only [Complex.ofReal_zero] at h
  rw [hk0, hf0] at h
  calc
    _ = (∫ u : ℝ, EF.weilTest f.1.1 f.1.1 u).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = _ := by rw [h, Complex.ofReal_re]

/-- Nonnegative correlation bounds both poles by actual width and source integral. -/
theorem joint_testPole_width_bounds (f : JointSmoothTest) {W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hW : 0 ≤ W)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re) :
    2*‖∫ u : ℝ, f.1.1 u‖^2 ≤ testPole f.1.1 ∧
    testPole f.1.1 ≤ 2*Real.cosh (W/2)*‖∫ u : ℝ, f.1.1 u‖^2 := by
  let q : ℝ → ℝ := fun u => (EF.weilTest f.1.1 f.1.1 u).re
  have hk := WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2
  have hqc : Continuous q := Complex.continuous_re.comp hk.cont
  have hqs : HasCompactSupport q := hk.supp.comp_left (g := Complex.re) (by simp)
  have hiq : Integrable q := hqc.integrable_of_hasCompactSupport hqs
  have hwc : Continuous (fun u : ℝ => 2*Real.cosh (u/2)*q u) := by fun_prop
  have hiw : Integrable (fun u : ℝ => 2*Real.cosh (u/2)*q u) :=
    hwc.integrable_of_hasCompactSupport hqs.mul_left
  have hlow (u : ℝ) : 2*q u ≤ 2*Real.cosh (u/2)*q u := by
    have hh := mul_le_mul_of_nonneg_right (Real.one_le_cosh (u/2)) (hq u)
    change 2*q u ≤ 2*Real.cosh (u/2)*q u
    dsimp [q] at *
    linarith
  have hup (u : ℝ) : 2*Real.cosh (u/2)*q u ≤ 2*Real.cosh (W/2)*q u := by
    by_cases hu : W < |u|
    · have hz : q u = 0 := by
        dsimp [q]
        rw [weilTest_eq_zero_outside_interval hf hu, Complex.zero_re]
      simp only [hz, mul_zero, le_refl]
    · have hub : |u| ≤ W := le_of_not_gt hu
      have hcos : Real.cosh (u/2) ≤ Real.cosh (W/2) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_div, abs_div, abs_of_nonneg hW]
        norm_num
        linarith
      have hh := mul_le_mul_of_nonneg_right hcos (hq u)
      dsimp [q] at *
      linarith
  have hl := integral_mono (hiq.const_mul 2) hiw hlow
  have hu := integral_mono hiw (hiq.const_mul (2*Real.cosh (W/2))) hup
  rw [integral_const_mul] at hl hu
  change _ ≤ ∫ u : ℝ, 2*Real.cosh (u/2)*(EF.weilTest f.1.1 f.1.1 u).re at hl
  change (∫ u : ℝ, 2*Real.cosh (u/2)*(EF.weilTest f.1.1 f.1.1 u).re) ≤ _ at hu
  rw [← testPole_eq_integral_cosh f.1] at hl hu
  change 2*(∫ u : ℝ, (EF.weilTest f.1.1 f.1.1 u).re) ≤ _ at hl
  change _ ≤ 2*Real.cosh (W/2)*(∫ u : ℝ, (EF.weilTest f.1.1 f.1.1 u).re) at hu
  rw [joint_integral_real_autocorr] at hl hu
  exact ⟨hl, hu⟩

/-- Quantitative pole remainder for the dilated source, uniform in its width. -/
theorem jointSeedPoleProfile_bounds (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re)
    {W : ℝ} (hW : 0 < W) :
    2*‖∫ u : ℝ, f.1.1 u‖^2 ≤ jointSeedPoleProfile f W ∧
    jointSeedPoleProfile f W ≤ 2*Real.cosh (W/2)*‖∫ u : ℝ, f.1.1 u‖^2 := by
  let g := jointDilatedTest f W hW
  have hg : tsupport g.1.1 ⊆ Icc 0 W := jointDilatedProfile_support hf hW
  have hqg (u : ℝ) : 0 ≤ (EF.weilTest g.1.1 g.1.1 u).re := by
    change 0 ≤ (EF.weilTest (jointDilatedProfile f.1.1 W)
      (jointDilatedProfile f.1.1 W) u).re
    rw [jointDilatedProfile_corr f.1.1 hW]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg hW.le (hq _)
  have hb := joint_testPole_width_bounds g hg hW.le hqg
  have hint : (∫ u : ℝ, g.1.1 u) = W • ∫ u : ℝ, f.1.1 u := by
    change (∫ u : ℝ, f.1.1 (W⁻¹*u)) = _
    rw [Measure.integral_comp_inv_mul_left f.1.1 W, abs_of_pos hW]
  have hp : testPole g.1.1 = W^2*jointSeedPoleProfile f W :=
    joint_dilated_pole_eq f hW
  rw [hint, hp, norm_smul, Real.norm_eq_abs, abs_of_pos hW, mul_pow] at hb
  constructor
  · nlinarith only [hb.1, sq_pos_of_pos hW]
  · nlinarith only [hb.2, sq_pos_of_pos hW]

/-- The explicit source pays correlation positivity; no source-sign input remains. -/
theorem jointUnitBumpPoleProfile_bounds {W : ℝ} (hW : 0 < W) :
    2*‖∫ u : ℝ, jointUnitBumpTest.1.1 u‖^2 ≤ jointSeedPoleProfile jointUnitBumpTest W ∧
    jointSeedPoleProfile jointUnitBumpTest W ≤
      2*Real.cosh (W/2)*‖∫ u : ℝ, jointUnitBumpTest.1.1 u‖^2 :=
  jointSeedPoleProfile_bounds jointUnitBumpTest jointUnitBumpTest_support
    jointUnitBumpTest_corr_nonneg hW

private theorem pole_cosh_half_error {W : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1) :
    Real.cosh (W/2)-1 ≤ W^2/4 := by
  have hx : |W/2| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  have hn := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (by simpa only [abs_neg] using hx : |-(W/2)| ≤ 1))).2
  rw [Real.cosh_eq]
  nlinarith only [hp, hn]

/-- An explicit quadratic remainder, sufficient for the logarithmic width boundary. -/
theorem jointSeedPoleProfile_error (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re)
    {W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) :
    |jointSeedPoleProfile f W-2*‖∫ u : ℝ, f.1.1 u‖^2| ≤
      ‖∫ u : ℝ, f.1.1 u‖^2*W^2/2 := by
  have hb := jointSeedPoleProfile_bounds f hf hq hW
  rw [abs_of_nonneg (sub_nonneg.mpr hb.1)]
  have hc := mul_le_mul_of_nonneg_left (pole_cosh_half_error hW.le hW1)
    (sq_nonneg ‖∫ u : ℝ, f.1.1 u‖)
  nlinarith only [hb.2, hc]

theorem jointUnitBumpPoleProfile_error {W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) :
    |jointSeedPoleProfile jointUnitBumpTest W-2*‖∫ u : ℝ, jointUnitBumpTest.1.1 u‖^2| ≤
      ‖∫ u : ℝ, jointUnitBumpTest.1.1 u‖^2*W^2/2 :=
  jointSeedPoleProfile_error jointUnitBumpTest jointUnitBumpTest_support
    jointUnitBumpTest_corr_nonneg hW hW1

end RHTower.WeilWorkPBAP
