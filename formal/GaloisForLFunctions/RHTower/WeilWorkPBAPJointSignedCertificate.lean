import GaloisForLFunctions.RHTower.WeilWorkPBAPJointContinuousCertificate
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointGammaFloor

/-!
# A continuous full-energy certificate for complex source profiles

Both signed poles are retained. Absolute autocorrelation mass pays a quartic
dilation remainder independently of modulation. Combined with the exact-mass
Gamma floor, this removes the correlation-sign restriction from the continuous
certificate. The integer-node transfer remains a separate obligation.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Literal absolute real-autocorrelation mass; it need not equal the zero Fourier value. -/
def jointAbsCorrMass (f : JointSmoothTest) : ℝ :=
  ∫ y : ℝ, |(EF.weilTest f.1.1 f.1.1 y).re|

theorem jointAbsCorrMass_nonneg (f : JointSmoothTest) : 0 ≤ jointAbsCorrMass f :=
  integral_nonneg fun _ => abs_nonneg _

/-- The absolute correlation mass stays positive even when the source integral vanishes. -/
theorem jointAbsCorrMass_pos (f : JointSmoothTest) (hf : f.1.1 ≠ 0) :
    0 < jointAbsCorrMass f := by
  have hk := WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2
  have hc : Continuous (fun y : ℝ => |(EF.weilTest f.1.1 f.1.1 y).re|) :=
    (Complex.continuous_re.comp hk.cont).abs
  have hs : HasCompactSupport (fun y : ℝ => |(EF.weilTest f.1.1 f.1.1 y).re|) :=
    hk.supp.comp_left (g := fun z : ℂ => |z.re|) (by simp)
  have h0 : |(EF.weilTest f.1.1 f.1.1 0).re| ≠ 0 := by
    rw [autocorr_zero_eq_testMass, Complex.ofReal_re, abs_of_pos (joint_testMass_pos f hf)]
    exact (joint_testMass_pos f hf).ne'
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hc hs
    (fun y => abs_nonneg _) h0

private theorem weighted_corr_integrable (f : JointSmoothTest) {w : ℝ → ℝ}
    (hw : Continuous w) : Integrable (fun y => w y*(EF.weilTest f.1.1 f.1.1 y).re) := by
  have hk := WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2
  exact (hw.mul (Complex.continuous_re.comp hk.cont)).integrable_of_hasCompactSupport
    (hk.supp.comp_left (g := Complex.re) (by simp)).mul_left

theorem jointAbsCorrMass_dilate (f : JointSmoothTest) {W : ℝ} (hW : 0 < W) :
    jointAbsCorrMass (jointDilatedTest f W hW)=W^2*jointAbsCorrMass f := by
  unfold jointAbsCorrMass
  change (∫ y : ℝ, |(EF.weilTest (jointDilatedProfile f.1.1 W)
    (jointDilatedProfile f.1.1 W) y).re|)=_
  simp_rw [jointDilatedProfile_corr f.1.1 hW, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_mul, abs_of_pos hW]
  rw [integral_const_mul,
    Measure.integral_comp_inv_mul_left (fun y => |(EF.weilTest f.1.1 f.1.1 y).re|) W,
    abs_of_pos hW, smul_eq_mul]
  ring

/-- Both signed poles collapse to the modulated actual autocorrelation. -/
theorem joint_pair_pole_eq_cosine_integral (f : JointSmoothTest) (L T : ℝ) :
    testPole (clusterDifference (cosineProfile f.1.1 T) L)+
      testPole (clusterDifference (sineProfile f.1.1 T) L)=
      -4*(Real.cosh (L/2)-1)*∫ y : ℝ,
        Real.cosh (y/2)*(EF.weilTest f.1.1 f.1.1 y).re*Real.cos (T*y) := by
  have hc := joint_cluster_pole_eq (cosineProfileTest f T) L
  have hs := joint_cluster_pole_eq (sineProfileTest f T) L
  dsimp only [cosineProfileTest] at hc
  dsimp only [sineProfileTest] at hs
  rw [hc, hs, ← mul_add]
  have hci := weighted_corr_integrable (cosineProfileTest f T)
    (show Continuous (fun y : ℝ => 2*Real.cosh (y/2)) by fun_prop)
  have hsi := weighted_corr_integrable (sineProfileTest f T)
    (show Continuous (fun y : ℝ => 2*Real.cosh (y/2)) by fun_prop)
  have hcp := testPole_eq_integral_cosh (cosineProfileTest f T).1
  have hsp := testPole_eq_integral_cosh (sineProfileTest f T).1
  dsimp only [cosineProfileTest] at hci hcp
  dsimp only [sineProfileTest] at hsi hsp
  rw [hcp, hsp, ← integral_add hci hsi]
  have he : (fun y : ℝ =>
      2*Real.cosh (y/2)*(EF.weilTest (cosineProfile f.1.1 T) (cosineProfile f.1.1 T) y).re+
      2*Real.cosh (y/2)*(EF.weilTest (sineProfile f.1.1 T) (sineProfile f.1.1 T) y).re)=
      (fun y => 2*(Real.cosh (y/2)*(EF.weilTest f.1.1 f.1.1 y).re*Real.cos (T*y))) := by
    funext y
    have h := congrArg Complex.re (weilTest_cosine_sine_add f.2.continuous f.1.2.2 T y)
    simp only [Complex.add_re, Complex.re_ofReal_mul] at h
    linear_combination 2*Real.cosh (y/2)*h
  rw [he, integral_const_mul]
  ring

private theorem cosh_error {y W : ℝ} (hy : |y| ≤ W) (hW1 : W ≤ 1) :
    |Real.cosh (y/2)-1| ≤ W^2/4 := by
  have hW : 0 ≤ W := (abs_nonneg y).trans hy
  have hx : |y/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have hp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  have hn := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (by simpa only [abs_neg] using hx : |-(y/2)| ≤ 1))).2
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _)), Real.cosh_eq]
  have hy2 : y^2 ≤ W^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hW).mpr hy
  nlinarith only [hp, hn, hy2]

/-- A quadratic width error, uniform in every modulation, with signed correlation. -/
theorem joint_pair_pole_cosine_error (f : JointSmoothTest) {W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hW1 : W ≤ 1) (L T : ℝ) :
    |testPole (clusterDifference (cosineProfile f.1.1 T) L)+
      testPole (clusterDifference (sineProfile f.1.1 T) L)+
      4*(Real.cosh (L/2)-1)*jointCosineIntegral f T| ≤
        (Real.cosh (L/2)-1)*W^2*jointAbsCorrMass f := by
  let r : ℝ → ℝ := fun y => (EF.weilTest f.1.1 f.1.1 y).re
  let e : ℝ → ℝ := fun y => (Real.cosh (y/2)-1)*r y*Real.cos (T*y)
  have hi : Integrable e := by
    have h := weighted_corr_integrable f
      (show Continuous (fun y : ℝ => (Real.cosh (y/2)-1)*Real.cos (T*y)) by fun_prop)
    exact h.congr (Eventually.of_forall fun y => by dsimp [e,r]; ring)
  have hr : Integrable r := by
    simpa only [one_mul] using weighted_corr_integrable f
      (show Continuous (fun _ : ℝ => (1:ℝ)) from continuous_const)
  have hbound (y : ℝ) : |e y| ≤ (W^2/4)*|r y| := by
    by_cases hy : W < |y|
    · have hz : r y=0 := by
        dsimp [r]; rw [weilTest_eq_zero_outside_interval hf hy, Complex.zero_re]
      simp only [e, hz, mul_zero, zero_mul, abs_zero, le_refl]
    · have hc := cosh_error (le_of_not_gt hy) hW1
      have hh : |e y| ≤ |Real.cosh (y/2)-1| * |r y| := by
        dsimp only [e]
        rw [abs_mul, abs_mul]
        exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (Real.abs_cos_le_one _)
      exact hh.trans (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
  have hb : |∫ y : ℝ, e y| ≤ (W^2/4)*jointAbsCorrMass f := by
    calc _ ≤ ∫ y : ℝ, |e y| := abs_integral_le_integral_abs
         _ ≤ ∫ y : ℝ, (W^2/4)*|r y| := integral_mono hi.abs (hr.abs.const_mul _) hbound
         _ = _ := by rw [integral_const_mul]; rfl
  have hcos : Integrable (fun y : ℝ => Real.cosh (y/2)*r y*Real.cos (T*y)) := by
    have h := weighted_corr_integrable f
      (show Continuous (fun y : ℝ => Real.cosh (y/2)*Real.cos (T*y)) by fun_prop)
    exact h.congr (Eventually.of_forall fun y => by dsimp [r]; ring)
  have hplain : Integrable (fun y : ℝ => r y*Real.cos (T*y)) := by
    have h := weighted_corr_integrable f
      (show Continuous (fun y : ℝ => Real.cos (T*y)) by fun_prop)
    exact h.congr (Eventually.of_forall fun y => by dsimp [r]; ring)
  have he : (∫ y : ℝ, e y)=(∫ y : ℝ, Real.cosh (y/2)*r y*Real.cos (T*y))-
      jointCosineIntegral f T := by
    change (∫ y : ℝ, e y)=(∫ y : ℝ, Real.cosh (y/2)*r y*Real.cos (T*y))-
      (∫ y : ℝ, r y*Real.cos (T*y))
    rw [← integral_sub hcos hplain]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by dsimp [e]; ring
  have hp : testPole (clusterDifference (cosineProfile f.1.1 T) L)+
      testPole (clusterDifference (sineProfile f.1.1 T) L)+
      4*(Real.cosh (L/2)-1)*jointCosineIntegral f T=
        -4*(Real.cosh (L/2)-1)*(∫ y : ℝ, e y) := by
    rw [joint_pair_pole_eq_cosine_integral, he]
    dsimp only [r]
    ring
  rw [hp, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _))]
  rw [show |(-4:ℝ)|=4 by norm_num]
  have hh := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sub_nonneg.mpr (Real.one_le_cosh (L/2))))
  calc
    _ ≤ 4*(Real.cosh (L/2)-1)*((W^2/4)*jointAbsCorrMass f) := hh
    _ = _ := by ring

/-- Actual dilation gives a quartic pole remainder with no correlation-sign premise. -/
theorem joint_dilated_pole_cosine_error (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) {W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) (L T : ℝ) :
    |testPole (clusterDifference (cosineProfile (jointDilatedProfile f.1.1 W) T) L)+
      testPole (clusterDifference (sineProfile (jointDilatedProfile f.1.1 W) T) L)+
      4*(Real.cosh (L/2)-1)*W^2*jointCosineIntegral f (W*T)| ≤
        (Real.cosh (L/2)-1)*W^4*jointAbsCorrMass f := by
  have h := joint_pair_pole_cosine_error (jointDilatedTest f W hW)
    (jointDilatedProfile_support hf hW) hW1 L T
  rw [jointCosineIntegral_dilate f hW, jointAbsCorrMass_dilate f hW] at h
  dsimp only [jointDilatedTest] at h
  have hpow : W^4=W^2*W^2 := by ring
  simpa only [hpow, mul_assoc] using h

/-- A continuous pole certificate for arbitrary complex source profiles. -/
theorem joint_dilated_signed_certificate (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) {W L : ℝ}
    (hW : 0 < W) (hW1 : W ≤ 1) (hWL : W < L) (T : ℝ) :
    -2*W*testMass f.1.1*Real.log W-W*jointGammaFloorCost f-
      (Real.cosh (L/2)-1)*W^4*jointAbsCorrMass f ≤
      jointPairFullEnergy (jointDilatedTest f W hW) L T+
        4*(Real.cosh (L/2)-1)*W^2*jointCosineIntegral f (W*T) := by
  have hg := joint_dilated_gamma_floor f hf hW hWL T
  have hp := (abs_le.mp (joint_dilated_pole_cosine_error f hf hW hW1 L T)).1
  have hc := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (cosineProfileTest (jointDilatedTest f W hW) T) L).1
  have hs := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (sineProfileTest (jointDilatedTest f W hW) T) L).1
  dsimp only [clusterDifferenceTest, cosineProfileTest, jointDilatedTest] at hc
  dsimp only [clusterDifferenceTest, sineProfileTest, jointDilatedTest] at hs
  dsimp only [jointPairFullEnergy, jointDilatedTest]
  linarith

end RHTower.WeilWorkPBAP
