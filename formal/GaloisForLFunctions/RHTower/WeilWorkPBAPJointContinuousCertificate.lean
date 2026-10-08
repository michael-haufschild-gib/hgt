import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedExpansion

/-!
# A continuous cosine certificate retaining both poles

The positive modulation kernel dominates its constant pole contribution.
The actual autocorrelation cosine integral therefore compensates the leading
negative pole uniformly in modulation. Integer quadrature is still required
to turn this continuous certificate into an integer-null certificate.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The literal cosine transform of the real autocorrelation. -/
def jointCosineIntegral (f : JointSmoothTest) (T : ℝ) : ℝ :=
  ∫ y : ℝ, (EF.weilTest f.1.1 f.1.1 y).re * Real.cos (T*y)

private theorem corr_integrable (f : JointSmoothTest) :
    Integrable (fun y : ℝ => (EF.weilTest f.1.1 f.1.1 y).re) := by
  have hk := WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2
  exact (hk.cont.integrable_of_hasCompactSupport hk.supp).re

private theorem corr_cos_integrable (f : JointSmoothTest) (T : ℝ) :
    Integrable (fun y : ℝ => (EF.weilTest f.1.1 f.1.1 y).re * Real.cos (T*y)) := by
  have hk := WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2
  have hqc : Continuous (fun y : ℝ => (EF.weilTest f.1.1 f.1.1 y).re) :=
    Complex.continuous_re.comp hk.cont
  have hc : Continuous (fun y : ℝ => (EF.weilTest f.1.1 f.1.1 y).re * Real.cos (T*y)) := by
    fun_prop
  exact hc.integrable_of_hasCompactSupport
    (hk.supp.comp_left (g := Complex.re) (by simp)).mul_right

theorem jointCosineIntegral_zero (f : JointSmoothTest) :
    jointCosineIntegral f 0 = ‖∫ y : ℝ, f.1.1 y‖^2 := by
  simpa only [jointCosineIntegral, zero_mul, Real.cos_zero, mul_one] using
    joint_integral_real_autocorr f

/-- Positivity follows from the two actual modulated autocorrelations. -/
theorem jointCosineIntegral_eq_pair (f : JointSmoothTest) (T : ℝ) :
    jointCosineIntegral f T =
      ‖∫ y : ℝ, cosineProfile f.1.1 T y‖^2 +
      ‖∫ y : ℝ, sineProfile f.1.1 T y‖^2 := by
  have hc := joint_integral_real_autocorr (cosineProfileTest f T)
  have hs := joint_integral_real_autocorr (sineProfileTest f T)
  change (∫ y : ℝ, (EF.weilTest (cosineProfile f.1.1 T) (cosineProfile f.1.1 T) y).re) = _ at hc
  change (∫ y : ℝ, (EF.weilTest (sineProfile f.1.1 T) (sineProfile f.1.1 T) y).re) = _ at hs
  dsimp only [cosineProfileTest] at hc
  dsimp only [sineProfileTest] at hs
  have hci := corr_integrable (cosineProfileTest f T)
  have hsi := corr_integrable (sineProfileTest f T)
  dsimp only [cosineProfileTest] at hci
  dsimp only [sineProfileTest] at hsi
  rw [← hc, ← hs, ← integral_add hci hsi]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    have h := congrArg Complex.re (weilTest_cosine_sine_add f.2.continuous f.1.2.2 T y)
    dsimp only [cosineProfileTest, sineProfileTest]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at h
    linarith

theorem jointCosineIntegral_nonneg (f : JointSmoothTest) (T : ℝ) :
    0 ≤ jointCosineIntegral f T := by
  rw [jointCosineIntegral_eq_pair]
  positivity

theorem jointCosineIntegral_le_zero (f : JointSmoothTest)
    (hq : ∀ y : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 y).re) (T : ℝ) :
    jointCosineIntegral f T ≤ jointCosineIntegral f 0 := by
  simp only [jointCosineIntegral, zero_mul, Real.cos_zero, mul_one]
  apply integral_mono (corr_cos_integrable f T) (corr_integrable f)
  intro y
  exact mul_le_of_le_one_right (hq y) (Real.cos_le_one _)

private theorem jump_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    archJump y ≤ archJump x := by
  have hdx : 0 < 1-Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hn : Real.exp (-(y/4)) ≤ Real.exp (-(x/4)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hd : 1-Real.exp (-x) ≤ 1-Real.exp (-y) := by
    have := Real.exp_le_exp.mpr (show -y ≤ -x by linarith)
    linarith
  unfold archJump
  exact div_le_div₀ (Real.exp_pos _).le hn hdx hd

/-- The full kernel pays the constant part of both poles pointwise. -/
theorem jointModulationKernel_pole_le {L y : ℝ} (hy : 0 < y) (hL : 2*y < L) :
    8*(Real.cosh (L/2)-1) ≤ jointModulationKernel L y := by
  have hp := jump_antitone (show 0 < 2*y by linarith)
    (show 2*y ≤ 2*(L+y) by linarith)
  have hm := jump_antitone (show 0 < 2*y by linarith)
    (show 2*y ≤ 2*(L-y) by linarith)
  have hc := mul_le_mul_of_nonneg_left (Real.one_le_cosh (y/2))
    (show 0 ≤ 8*(Real.cosh (L/2)-1) by nlinarith [Real.one_le_cosh (L/2)])
  unfold jointModulationKernel
  linarith

/-- A continuous certificate for the exact full energy, with no energy-sign premise. -/
theorem jointPairFullEnergy_continuous_certificate (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hW : 0 < W) (hL : 2*W < L)
    (hq : ∀ y : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 y).re) (T : ℝ) :
    jointPairFullEnergy f L 0 + 4*(Real.cosh (L/2)-1)*jointCosineIntegral f 0 ≤
      jointPairFullEnergy f L T + 4*(Real.cosh (L/2)-1)*jointCosineIntegral f T := by
  let g : ℝ → ℝ := fun y => (EF.weilTest f.1.1 f.1.1 y).re*(1-Real.cos (T*y))
  let C : ℝ := Real.cosh (L/2)-1
  have hC : 0 ≤ C := sub_nonneg.mpr (Real.one_le_cosh _)
  have hg0 (y : ℝ) : 0 ≤ g y :=
    mul_nonneg (hq y) (by linarith [Real.cos_le_one (T*y)])
  have hk := WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2
  have hqc : Continuous (fun y : ℝ => (EF.weilTest f.1.1 f.1.1 y).re) :=
    Complex.continuous_re.comp hk.cont
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hgs : HasCompactSupport g :=
    (hk.supp.comp_left (g := Complex.re) (by simp)).mul_right
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hci : Integrable (fun y : ℝ => Real.cosh (y/2)*g y) :=
    ((by fun_prop : Continuous fun y : ℝ => Real.cosh (y/2)).mul hgc).integrable_of_hasCompactSupport
      hgs.mul_left
  have hji : IntegrableOn (fun y : ℝ => archJump (2*y)*g y) (Ioi 0) := by
    simpa only [g, mul_assoc] using integrable_modulation_jump f T
  have hb (y : ℝ) (hy : y ∈ Ioi (0:ℝ)) :
      8*C*g y ≤ jointModulationKernel L y*g y ∧
      jointModulationKernel L y*g y ≤
        4*(archJump (2*y)*g y)+8*C*(Real.cosh (y/2)*g y) := by
    have hy0 : 0 < y := hy
    by_cases hyW : y ≤ W
    · have hl : 2*y < L := by linarith
      have hlo := mul_le_mul_of_nonneg_right (jointModulationKernel_pole_le hy0 hl) (hg0 y)
      have hp := archJump_nonneg (show 0 < 2*(L+y) by linarith)
      have hm := archJump_nonneg (show 0 < 2*(L-y) by linarith)
      have hup : jointModulationKernel L y ≤
          4*archJump (2*y)+8*C*Real.cosh (y/2) := by
        dsimp [jointModulationKernel, C]
        linarith
      exact ⟨hlo, (mul_le_mul_of_nonneg_right hup (hg0 y)).trans_eq (by ring)⟩
    · have hz := weilTest_eq_zero_outside_interval hf
        (show W < |y| by rw [abs_of_pos hy0]; exact lt_of_not_ge hyW)
      simp [g, hz]
  have hmi : AEStronglyMeasurable (fun y : ℝ => jointModulationKernel L y*g y)
      (volume.restrict (Ioi 0)) := by
    have hm : Measurable (fun y : ℝ => jointModulationKernel L y*g y) := by
      dsimp [jointModulationKernel, archJump]
      fun_prop
    exact hm.aestronglyMeasurable
  have hki : IntegrableOn (fun y : ℝ => jointModulationKernel L y*g y) (Ioi 0) := by
    apply ((hji.const_mul 4).add (hci.integrableOn.const_mul (8*C))).mono' hmi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have h := hb y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans
      (mul_nonneg (mul_nonneg (by norm_num) hC) (hg0 y)) h.1)]
    exact h.2
  have hi := integral_mono_ae (hgi.integrableOn.const_mul (8*C)) hki
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; exact (hb y hy).1)
  rw [integral_const_mul] at hi
  have heven (y : ℝ) : g (-y)=g y := by
    dsimp [g]
    rw [weilTest_self_neg, Complex.conj_re, mul_neg, Real.cos_neg]
  have hsplit := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hgi
  have hneg := integral_comp_neg_Ioi 0 g
  simp only [heven, neg_zero] at hneg
  rw [compl_Ioi, ← hneg] at hsplit
  have hdef : (∫ y : ℝ, g y)=jointCosineIntegral f 0-jointCosineIntegral f T := by
    simp only [g, mul_sub, mul_one]
    rw [integral_sub (corr_integrable f) (corr_cos_integrable f T)]
    simp only [jointCosineIntegral, zero_mul, Real.cos_zero, mul_one]
  have he := jointPairFullEnergy_sub_zero f hf hW hL T
  have he' : jointPairFullEnergy f L T-jointPairFullEnergy f L 0 =
      ∫ y in Ioi (0:ℝ), jointModulationKernel L y*g y := by
    simpa only [g, mul_assoc] using he
  rw [← he'] at hi
  rw [hdef] at hsplit
  dsimp only [C] at hi hsplit
  nlinarith

/-- Dilation retains the complete cosine transform, including its squared width. -/
theorem jointCosineIntegral_dilate (f : JointSmoothTest) {W : ℝ} (hW : 0 < W) (T : ℝ) :
    jointCosineIntegral (jointDilatedTest f W hW) T =
      W^2*jointCosineIntegral f (W*T) := by
  change (∫ y : ℝ, (EF.weilTest (jointDilatedProfile f.1.1 W)
    (jointDilatedProfile f.1.1 W) y).re * Real.cos (T*y)) = _
  simp_rw [jointDilatedProfile_corr f.1.1 hW]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have ht (y : ℝ) : (W*T)*(W⁻¹*y)=T*y := by field_simp
  have he : (fun y : ℝ => W*(EF.weilTest f.1.1 f.1.1 (W⁻¹*y)).re*Real.cos (T*y)) =
      fun y : ℝ => W*((fun v : ℝ =>
        (EF.weilTest f.1.1 f.1.1 v).re*Real.cos (W*T*v)) (W⁻¹*y)) := by
    funext y
    dsimp only
    rw [ht y]
    ring
  rw [he, integral_const_mul,
    Measure.integral_comp_inv_mul_left
      (fun y : ℝ => (EF.weilTest f.1.1 f.1.1 y).re*Real.cos (W*T*y)) W,
    abs_of_pos hW]
  simp only [smul_eq_mul, jointCosineIntegral]
  ring

/-- A uniform actual-source lower bound after the continuous pole correction. -/
theorem joint_dilated_continuous_certificate (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ y : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 y).re)
    {L W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) (hL : 2*W < L) (T : ℝ) :
    -2*W*testMass f.1.1*Real.log W-W*jointSeedLogCost f-
      (Real.cosh (L/2)-1)*W^4*‖∫ u : ℝ, f.1.1 u‖^2 ≤
      jointPairFullEnergy (jointDilatedTest f W hW) L T+
        4*(Real.cosh (L/2)-1)*W^2*jointCosineIntegral f (W*T) := by
  have hqd (y : ℝ) :
      0 ≤ (EF.weilTest (jointDilatedTest f W hW).1.1
        (jointDilatedTest f W hW).1.1 y).re := by
    change 0 ≤ (EF.weilTest (jointDilatedProfile f.1.1 W)
      (jointDilatedProfile f.1.1 W) y).re
    rw [jointDilatedProfile_corr f.1.1 hW]
    simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using mul_nonneg hW.le (hq (W⁻¹*y))
  have hc := jointPairFullEnergy_continuous_certificate (jointDilatedTest f W hW)
    (jointDilatedProfile_support hf hW) hW hL hqd T
  rw [jointCosineIntegral_dilate f hW 0, jointCosineIntegral_dilate f hW T,
    mul_zero, jointCosineIntegral_zero] at hc
  have hs := (abs_le.mp (joint_seed_full_expansion f hf hq hW hW1
    (show W < L by linarith))).1
  nlinarith

theorem jointUnitBump_continuous_certificate {L W : ℝ}
    (hW : 0 < W) (hW1 : W ≤ 1) (hL : 2*W < L) (T : ℝ) :
    -2*W*testMass jointUnitBumpTest.1.1*Real.log W-W*jointSeedLogCost jointUnitBumpTest-
      (Real.cosh (L/2)-1)*W^4*‖∫ u : ℝ, jointUnitBumpTest.1.1 u‖^2 ≤
      jointPairFullEnergy (jointDilatedTest jointUnitBumpTest W hW) L T+
        4*(Real.cosh (L/2)-1)*W^2*jointCosineIntegral jointUnitBumpTest (W*T) :=
  joint_dilated_continuous_certificate jointUnitBumpTest jointUnitBumpTest_support
    jointUnitBumpTest_corr_nonneg hW hW1 hL T

end RHTower.WeilWorkPBAP
