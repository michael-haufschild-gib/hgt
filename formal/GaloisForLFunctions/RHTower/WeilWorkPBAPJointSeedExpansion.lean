import GaloisForLFunctions.RHTower.WeilWorkPBAPJointPoleBounds

/-!
# Uniform full seed expansion through the logarithmic width correction

The actual Gamma remainder is O(W), while the two-pole remainder is bounded
by (cosh(L/2)-1) W^4 times the squared source integral. These explicit bounds
are uniform in L and W and do not replace a continuity statement by a rate.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

theorem joint_seed_pole_error (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re)
    {W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) (L : ℝ) :
    |testPole (clusterDifference (jointDilatedProfile f.1.1 W) L) +
      4*(Real.cosh (L/2)-1)*W^2*‖∫ u : ℝ, f.1.1 u‖^2| ≤
      (Real.cosh (L/2)-1)*W^4*‖∫ u : ℝ, f.1.1 u‖^2 := by
  have hA : 0 ≤ Real.cosh (L/2)-1 := sub_nonneg.mpr (Real.one_le_cosh _)
  have he := jointSeedPoleProfile_error f hf hq hW hW1
  rw [joint_seed_pole_eq f hW]
  have hid : -2*(Real.cosh (L/2)-1)*W^2*jointSeedPoleProfile f W+
      4*(Real.cosh (L/2)-1)*W^2*‖∫ u : ℝ, f.1.1 u‖^2 =
      -(2*(Real.cosh (L/2)-1)*W^2)*
        (jointSeedPoleProfile f W-2*‖∫ u : ℝ, f.1.1 u‖^2) := by ring
  rw [hid, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2*(Real.cosh (L/2)-1)*W^2)*(‖∫ u : ℝ, f.1.1 u‖^2*W^2/2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- Exact full energy, with a quantitative error uniform in separation and width. -/
theorem joint_seed_full_expansion (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re)
    {L W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) (hWL : W < L) :
    |jointPairFullEnergy (jointDilatedTest f W hW) L 0 +
      2*W*testMass f.1.1*Real.log W +
      4*(Real.cosh (L/2)-1)*W^2*‖∫ u : ℝ, f.1.1 u‖^2| ≤
      W*jointSeedLogCost f +
        (Real.cosh (L/2)-1)*W^4*‖∫ u : ℝ, f.1.1 u‖^2 := by
  have hg := joint_cluster_gamma_scale_mass_bound f hf hW hW1 hWL
  have hp := joint_seed_pole_error f hf hq hW hW1 L
  have henergy := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (jointDilatedTest f W hW) L).1
  dsimp only [clusterDifferenceTest, jointDilatedTest] at henergy
  rw [jointPairFullEnergy_zero]
  change |weilArchRe (EF.weilTest (clusterDifference (jointDilatedProfile f.1.1 W) L)
    (clusterDifference (jointDilatedProfile f.1.1 W) L)) + _ + _| ≤ _
  rw [henergy]
  calc
    _ = |(testGamma (clusterDifference (jointDilatedProfile f.1.1 W) L)+
      2*W*testMass f.1.1*Real.log W) +
      (testPole (clusterDifference (jointDilatedProfile f.1.1 W) L)+
      4*(Real.cosh (L/2)-1)*W^2*‖∫ u : ℝ, f.1.1 u‖^2)| := by congr 1; ring
    _ ≤ |testGamma (clusterDifference (jointDilatedProfile f.1.1 W) L)+
      2*W*testMass f.1.1*Real.log W| +
      |testPole (clusterDifference (jointDilatedProfile f.1.1 W) L)+
      4*(Real.cosh (L/2)-1)*W^2*‖∫ u : ℝ, f.1.1 u‖^2| := abs_add_le _ _
    _ ≤ _ := add_le_add hg hp

theorem jointUnitBump_seed_full_expansion {L W : ℝ}
    (hW : 0 < W) (hW1 : W ≤ 1) (hWL : W < L) :
    |jointPairFullEnergy (jointDilatedTest jointUnitBumpTest W hW) L 0 +
      2*W*testMass jointUnitBumpTest.1.1*Real.log W +
      4*(Real.cosh (L/2)-1)*W^2*‖∫ u : ℝ, jointUnitBumpTest.1.1 u‖^2| ≤
      W*jointSeedLogCost jointUnitBumpTest +
        (Real.cosh (L/2)-1)*W^4*‖∫ u : ℝ, jointUnitBumpTest.1.1 u‖^2 :=
  joint_seed_full_expansion jointUnitBumpTest jointUnitBumpTest_support
    jointUnitBumpTest_corr_nonneg hW hW1 hWL

end RHTower.WeilWorkPBAP
