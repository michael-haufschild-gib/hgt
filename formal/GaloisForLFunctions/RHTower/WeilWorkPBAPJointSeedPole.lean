import GaloisForLFunctions.RHTower.WeilWorkPBAPJointScale

/-!
# Exact signed pole scaling for actual cluster seeds

Both poles are retained. Cluster separation contributes an exact hyperbolic
factor; dilation contributes width squared times a continuous source profile.
The profile at zero is twice the squared source integral, with no sign premise.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Both pole terms are the real pairing of the two opposite Fourier evaluations. -/
theorem joint_testPole_eq_two_re (f : JointSmoothTest) :
    testPole f.1.1=2*(paperFT f.1.1 (I/2)*conj (paperFT f.1.1 (-I/2))).re := by
  have hp := EF.paperFT_weilTest f.2.continuous f.2.continuous f.1.2.2 f.1.2.2 (I/2)
  have hm := EF.paperFT_weilTest f.2.continuous f.2.continuous f.1.2.2 f.1.2.2 (-I/2)
  have hcp : conj (I/2:ℂ) = -I/2 := by
    simp only [map_div₀, map_ofNat, Complex.conj_I]
  have hcm : conj (-I/2:ℂ) = I/2 := by
    simp only [map_div₀, map_ofNat, map_neg, Complex.conj_I, neg_neg]
  rw [hcp] at hp
  rw [hcm] at hm
  unfold testPole
  rw [hp, hm, Complex.add_re]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The signed cluster pole factor is exact for every complex source profile. -/
theorem joint_cluster_pole_eq (f : JointSmoothTest) (L : ℝ) :
    testPole (clusterDifference f.1.1 L)=2*(1-Real.cosh (L/2))*testPole f.1.1 := by
  have ep : I*(I/2:ℂ)*L=((-L/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]; ring
  have em : I*(-I/2:ℂ)*L=((L/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]; ring
  have hp : paperFT (clusterDifference f.1.1 L) (I/2)=
      ((1-Real.exp (-L/2):ℝ):ℂ)*paperFT f.1.1 (I/2) := by
    rw [paperFT_clusterDifference f.2.continuous f.1.2.2, ep, ← Complex.ofReal_exp]
    push_cast
    rfl
  have hm : paperFT (clusterDifference f.1.1 L) (-I/2)=
      ((1-Real.exp (L/2):ℝ):ℂ)*paperFT f.1.1 (-I/2) := by
    rw [paperFT_clusterDifference f.2.continuous f.1.2.2, em, ← Complex.ofReal_exp]
    push_cast
    rfl
  have he : Real.exp (-L/2)*Real.exp (L/2)=1 := by
    rw [← Real.exp_add, show -L/2+L/2=0 by ring, Real.exp_zero]
  have hc : (1-Real.exp (-L/2))*(1-Real.exp (L/2))=2*(1-Real.cosh (L/2)) := by
    rw [Real.cosh_eq]
    have hn : -(L/2) = -L/2 := by ring
    rw [hn]
    nlinarith
  have ht := joint_testPole_eq_two_re (clusterDifferenceTest f L)
  change testPole (clusterDifference f.1.1 L)=
    2*(paperFT (clusterDifference f.1.1 L) (I/2)*
      conj (paperFT (clusterDifference f.1.1 L) (-I/2))).re at ht
  rw [ht, joint_testPole_eq_two_re f, hp, hm]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im]
  linear_combination
    (2*((paperFT f.1.1 (I/2)).re*(conj (paperFT f.1.1 (-I/2))).re-
      (paperFT f.1.1 (I/2)).im*(conj (paperFT f.1.1 (-I/2))).im))*hc

/-- A continuous source-defined pole profile; its value at zero is proved below. -/
def jointSeedPoleProfile (f : JointSmoothTest) (W : ℝ) : ℝ :=
  2*(paperFT f.1.1 ((W:ℂ)*(I/2))*conj (paperFT f.1.1 ((W:ℂ)*(-I/2)))).re

theorem continuous_jointSeedPoleProfile (f : JointSmoothTest) :
    Continuous (jointSeedPoleProfile f) := by
  have hF : Continuous (paperFT f.1.1) :=
    (Zeta23.WeilEF.differentiable_paperFT f.2.continuous f.1.2.2).continuous
  unfold jointSeedPoleProfile
  fun_prop

/-- The limiting profile is twice the squared literal source integral. -/
theorem jointSeedPoleProfile_zero (f : JointSmoothTest) :
    jointSeedPoleProfile f 0=2*‖∫ u : ℝ, f.1.1 u‖^2 := by
  simp only [jointSeedPoleProfile, Complex.ofReal_zero, zero_mul]
  have hF : paperFT f.1.1 0=∫ u : ℝ, f.1.1 u := by simp [paperFT_def]
  rw [hF, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Exact width-squared scaling of the full signed pole expression. -/
theorem joint_dilated_pole_eq (f : JointSmoothTest) {W : ℝ} (hW : 0 < W) :
    testPole (jointDilatedProfile f.1.1 W)=W^2*jointSeedPoleProfile f W := by
  have h := joint_testPole_eq_two_re (jointDilatedTest f W hW)
  change testPole (jointDilatedProfile f.1.1 W)=
    2*(paperFT (jointDilatedProfile f.1.1 W) (I/2)*
      conj (paperFT (jointDilatedProfile f.1.1 W) (-I/2))).re at h
  rw [h, jointDilatedProfile_paperFT f.1.1 hW, jointDilatedProfile_paperFT f.1.1 hW]
  simp only [jointSeedPoleProfile, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.mul_im]
  ring

/-- Literal two-cluster poles in the shrinking-width family. -/
theorem joint_seed_pole_eq (f : JointSmoothTest) {W : ℝ} (hW : 0 < W) (L : ℝ) :
    testPole (clusterDifference (jointDilatedProfile f.1.1 W) L)=
      -2*(Real.cosh (L/2)-1)*W^2*jointSeedPoleProfile f W := by
  have h := joint_cluster_pole_eq (jointDilatedTest f W hW) L
  change testPole (clusterDifference (jointDilatedProfile f.1.1 W) L)=
    2*(1-Real.cosh (L/2))*testPole (jointDilatedProfile f.1.1 W) at h
  rw [h, joint_dilated_pole_eq f hW]
  ring

theorem tendsto_jointSeedPoleProfile_zero (f : JointSmoothTest) :
    Tendsto (jointSeedPoleProfile f) (𝓝 0) (𝓝 (2*‖∫ u : ℝ, f.1.1 u‖^2)) := by
  rw [← jointSeedPoleProfile_zero]
  exact (continuous_jointSeedPoleProfile f).tendsto 0

end RHTower.WeilWorkPBAP
