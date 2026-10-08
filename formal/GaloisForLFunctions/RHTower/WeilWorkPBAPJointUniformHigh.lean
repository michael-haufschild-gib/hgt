import GaloisForLFunctions.RHTower.WeilWorkPBAPJointUpper
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointWidthSector

/-!
# Uniform logarithmic energy above the shrinking-width frequency threshold

The literal full energy retains its exact coefficient 2 in front of log |T|.
The bounds hold simultaneously for every width between kappa*L*exp(-L/2)
and 1. All remainders are explicit source costs tending uniformly to zero.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem uniform_gamma_error {κ L T W m C : ℝ}
    (hκ : 0 < κ) (hL : 1 ≤ L) (hm : 0 < m) (hC : 0 ≤ C)
    (hW : jointSeedWidth κ L ≤ W) (hT : Real.exp (7*L/8) ≤ T) :
    (C/(W^2*T^2))/(W*m) ≤ (C/(κ^3*m))*L*Real.exp (-L/4) := by
  have hLp : 0 < L := by linarith
  have hW0 := jointSeedWidth_pos hκ hLp
  have hWp : 0 < W := hW0.trans_le hW
  have hTp : 0 < T := (Real.exp_pos _).trans_le hT
  have h := joint_width_gamma_error_le hκ hL hm hC hT
  calc
    _ ≤ (C/((jointSeedWidth κ L)^2*T^2))/(jointSeedWidth κ L*m) := by gcongr
    _ = ((C/((jointSeedWidth κ L)^2*T^2))/(jointSeedWidth κ L*m*L))*L := by field_simp
    _ ≤ ((C/(κ^3*m))*Real.exp (-L/4))*L := mul_le_mul_of_nonneg_right h hLp.le
    _ = _ := by ring

private theorem uniform_pole_error {κ L T W m C : ℝ}
    (hκ : 0 < κ) (hL : 1 ≤ L) (hm : 0 < m) (hC : 0 ≤ C)
    (hW : jointSeedWidth κ L ≤ W) (hT : Real.exp (7*L/8) ≤ T) :
    (C*Real.exp (L/2)/(W^2*T^4))/(W*m) ≤
      (C/(κ^3*m))*L*Real.exp (-3*L/2) := by
  have hLp : 0 < L := by linarith
  have hW0 := jointSeedWidth_pos hκ hLp
  have hWp : 0 < W := hW0.trans_le hW
  have hTp : 0 < T := (Real.exp_pos _).trans_le hT
  have h := joint_width_pole_error_le hκ hL hm hC hT
  calc
    _ ≤ (C*Real.exp (L/2)/((jointSeedWidth κ L)^2*T^4))/(jointSeedWidth κ L*m) := by gcongr
    _ = ((C*Real.exp (L/2)/((jointSeedWidth κ L)^2*T^4))/(jointSeedWidth κ L*m*L))*L := by field_simp
    _ ≤ ((C/(κ^3*m))*Real.exp (-3*L/2))*L := mul_le_mul_of_nonneg_right h hLp.le
    _ = _ := by ring

/-- Explicit high-frequency remainder, normalized by actual dilated source mass. -/
def jointUniformHighRemainder (f : JointSmoothTest) (κ L : ℝ) : ℝ :=
  jointWidthGammaCost f κ*L*Real.exp (-L/4)+
    jointWidthPoleCost f κ*L*Real.exp (-3*L/2)

/-- The uniform remainder vanishes without losing the logarithmic main coefficient. -/
theorem tendsto_jointUniformHighRemainder_zero (f : JointSmoothTest) (κ : ℝ) :
    Tendsto (jointUniformHighRemainder f κ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℝ => L*Real.exp (-L/4)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/4) (by norm_num) using 1
    funext L
    rw [Real.rpow_one]
    congr 2
    ring
  have h2 : Tendsto (fun L : ℝ => L*Real.exp (-3*L/2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3/2) (by norm_num) using 1
    funext L
    rw [Real.rpow_one]
    congr 2
    ring
  have ht := (h1.const_mul (jointWidthGammaCost f κ)).add
    (h2.const_mul (jointWidthPoleCost f κ))
  change Tendsto (fun L => jointUniformHighRemainder f κ L) atTop (𝓝 0)
  simpa only [jointUniformHighRemainder, mul_assoc, mul_zero, add_zero] using ht

/-- Sharp high-frequency coefficient, uniformly for a whole interval of widths. -/
theorem joint_uniform_high_lower (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) (hm : 0 < testMass f.1.1)
    {κ L W T : ℝ} (hκ : 0 < κ) (hL : 2 ≤ L)
    (hW : 0 < W) (hWlo : jointSeedWidth κ L ≤ W) (hW1 : W ≤ 1)
    (hT : Real.exp (7*L/8) ≤ T) :
    2*Real.log T-2*(Real.log 2+10+Real.log 4)-jointUniformHighRemainder f κ L ≤
      jointPairFullEnergy (jointDilatedTest f W hW) L T/(W*testMass f.1.1) := by
  have hTp : 0 < T := (Real.exp_pos _).trans_le hT
  have hT2 : 2 ≤ T := by linarith [Real.add_one_le_exp (7*L/8)]
  have hd : 0 < W*testMass f.1.1 := mul_pos hW hm
  have h := div_le_div_of_nonneg_right
    (joint_dilated_pair_high_simple f hf (L:=L) (T:=T) hW hW1 (by linarith) hT2) hd.le
  rw [sub_div, sub_div] at h
  have hg := uniform_gamma_error (C:=64*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(2*Real.pi))
    hκ (by linarith : 1≤L) hm (by positivity) hWlo hT
  have hp := uniform_pole_error (C:=16*Real.exp 1*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2)
    hκ (by linarith : 1≤L) hm (by positivity) hWlo hT
  have hp' : (16*Real.exp (L/2+1)*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(W^2*T^4))/
      (W*testMass f.1.1) ≤ jointWidthPoleCost f κ*L*Real.exp (-3*L/2) := by
    unfold jointWidthPoleCost
    convert hp using 1
    rw [Real.exp_add]
    ring
  have hmain : (2*W*testMass f.1.1*(Real.log (T/2)-(10+Real.log 4)))/
      (W*testMass f.1.1) = 2*Real.log T-2*(Real.log 2+10+Real.log 4) := by
    rw [Real.log_div hTp.ne' (by norm_num : (2:ℝ)≠0)]
    field_simp
    ring
  rw [hmain] at h
  change _ ≤ jointWidthGammaCost f κ*L*Real.exp (-L/4) at hg
  unfold jointUniformHighRemainder
  linarith only [h,hg,hp']

/-- One threshold controls every allowed width and every signed high frequency. -/
theorem eventually_joint_uniform_high_lower (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) (hm : 0 < testMass f.1.1)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, ∀ (W : ℝ) (hW : 0 < W),
      jointSeedWidth κ L ≤ W → W ≤ 1 → ∀ T : ℝ, Real.exp (7*L/8) ≤ |T| →
      2*Real.log |T|-(2*(Real.log 2+10+Real.log 4)+1) ≤
        jointPairFullEnergy (jointDilatedTest f W hW) L T/(W*testMass f.1.1) := by
  have herr := (tendsto_jointUniformHighRemainder_zero f κ).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [herr,eventually_ge_atTop (3:ℝ)] with L herr hL
  intro W hW hWlo hW1 T hT
  have h := joint_uniform_high_lower f hf hm hκ (by linarith) hW hWlo hW1 hT
  have heq : jointPairFullEnergy (jointDilatedTest f W hW) L |T| =
      jointPairFullEnergy (jointDilatedTest f W hW) L T := by
    rcases le_total 0 T with hT0 | hT0
    · rw [abs_of_nonneg hT0]
    · rw [abs_of_nonpos hT0]
      exact jointPairFullEnergy_neg _ (jointDilatedProfile_support hf hW) hW (by linarith) T
  rw [heq] at h
  linarith only [h,herr]

private theorem uniform_first_error {κ L T W m C : ℝ}
    (hκ : 0 < κ) (hL : 1 ≤ L) (hm : 0 < m) (hC : 0 ≤ C)
    (hW : jointSeedWidth κ L ≤ W) (hT : Real.exp (7*L/8) ≤ T) :
    (C/(1+T))/(W*m) ≤ (C/(κ*m))*Real.exp (-3*L/8) := by
  have hLp : 0 < L := by linarith
  have hW0 := jointSeedWidth_pos hκ hLp
  have hWp : 0 < W := hW0.trans_le hW
  have hTp : 0 < T := (Real.exp_pos _).trans_le hT
  have he : Real.exp (-L/2)*Real.exp (7*L/8)*Real.exp (-3*L/8)=1 := by
    rw [← Real.exp_add, ← Real.exp_add, show -L/2+7*L/8+-3*L/8=0 by ring,Real.exp_zero]
  have hi : 1/(jointSeedWidth κ L*Real.exp (7*L/8)) =
      Real.exp (-3*L/8)/(κ*L) := by
    unfold jointSeedWidth
    field_simp
    convert he.symm using 1; ring_nf
  calc
    _ ≤ (C/Real.exp (7*L/8))/(jointSeedWidth κ L*m) := by gcongr; linarith
    _ = (C/m)*(1/(jointSeedWidth κ L*Real.exp (7*L/8))) := by ring
    _ = (C/(κ*m))*(Real.exp (-3*L/8)/L) := by rw [hi]; ring
    _ ≤ (C/(κ*m))*Real.exp (-3*L/8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_self (Real.exp_pos _).le hL

/-- Explicit first-moment and signed-pole costs in the uniform upper bound. -/
def jointUniformUpperRemainder (f : JointSmoothTest) (κ L : ℝ) : ℝ :=
  (4*jointFourierFirstMoment f.1.1/(2*Real.pi*κ*testMass f.1.1))*Real.exp (-3*L/8)+
    jointWidthPoleCost f κ*L*Real.exp (-3*L/2)

theorem tendsto_jointUniformUpperRemainder_zero (f : JointSmoothTest) (κ : ℝ) :
    Tendsto (jointUniformUpperRemainder f κ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℝ => Real.exp (-3*L/8)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (3/8) (by norm_num) using 1
    funext L
    rw [Real.rpow_zero,one_mul]
    congr 1
    ring
  have h2 : Tendsto (fun L : ℝ => L*Real.exp (-3*L/2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3/2) (by norm_num) using 1
    funext L
    rw [Real.rpow_one]
    congr 2
    ring
  have ht := (h1.const_mul (4*jointFourierFirstMoment f.1.1/(2*Real.pi*κ*testMass f.1.1))).add
    (h2.const_mul (jointWidthPoleCost f κ))
  change Tendsto (fun L => jointUniformUpperRemainder f κ L) atTop (𝓝 0)
  simpa only [jointUniformUpperRemainder,mul_assoc,mul_zero,add_zero] using ht

/-- Upper control for every allowed width, with actual Fourier first moment. -/
theorem joint_uniform_high_upper (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) (hm : 0 < testMass f.1.1)
    {κ L W T : ℝ} (hκ : 0 < κ) (hL : 2 ≤ L)
    (hW : 0 < W) (hWlo : jointSeedWidth κ L ≤ W) (hW1 : W ≤ 1)
    (hT : Real.exp (7*L/8) ≤ T) :
    jointPairFullEnergy (jointDilatedTest f W hW) L T/(W*testMass f.1.1) ≤
      2*Real.log (1+T)+8+jointUniformUpperRemainder f κ L := by
  have hTp : 0 < T := (Real.exp_pos _).trans_le hT
  have hLp : 0 ≤ L := by linarith
  have hd : 0 < W*testMass f.1.1 := mul_pos hW hm
  have h := joint_pair_full_energy_upper (jointDilatedTest f W hW)
    (L:=L) (T:=T) (jointDilatedProfile_support hf hW) (by linarith) hLp hTp
  change jointPairFullEnergy (jointDilatedTest f W hW) L T ≤
    2*testMass (jointDilatedProfile f.1.1 W)*(Real.log (1+T)+4)+
    4*jointFourierFirstMoment (jointDilatedProfile f.1.1 W)/(2*Real.pi*(1+T))+
    4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
      (Real.exp (W/2)*(∫u:ℝ,‖deriv (deriv (jointDilatedProfile f.1.1 W)) u‖)/T^2)^2 at h
  rw [jointDilatedProfile_mass f.1.1 hW,jointFourierFirstMoment_dilate f.1.1 hW,
    jointDilatedProfile_deriv_two_norm f.1.1 hW] at h
  have hp0 := joint_scaled_pole_loss_le (T:=T) (D:=∫u:ℝ,‖deriv (deriv f.1.1) u‖) hW1 hLp
  have hp := uniform_pole_error (C:=16*Real.exp 1*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2)
    hκ (by linarith : 1≤L) hm (by positivity) hWlo hT
  have hg := uniform_first_error (C:=4*jointFourierFirstMoment f.1.1/(2*Real.pi))
    hκ (by linarith : 1≤L) hm
    (by have := jointFourierFirstMoment_nonneg f.1.1; positivity) hWlo hT
  have hp' : (16*Real.exp (L/2+1)*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(W^2*T^4))/
      (W*testMass f.1.1) ≤ jointWidthPoleCost f κ*L*Real.exp (-3*L/2) := by
    unfold jointWidthPoleCost
    convert hp using 1
    rw [Real.exp_add]
    ring
  have hg' : (4*jointFourierFirstMoment f.1.1/(2*Real.pi*(1+T)))/(W*testMass f.1.1) ≤
      (4*jointFourierFirstMoment f.1.1/(2*Real.pi*κ*testMass f.1.1))*Real.exp (-3*L/8) := by
    convert hg using 1 <;> field_simp
  have he := div_le_div_of_nonneg_right h hd.le
  have hp0' := div_le_div_of_nonneg_right hp0 hd.le
  rw [add_div,add_div] at he
  have hmain : (2*(W*testMass f.1.1)*(Real.log (1+T)+4))/(W*testMass f.1.1) =
      2*Real.log (1+T)+8 := by field_simp; ring
  rw [hmain] at he
  unfold jointUniformUpperRemainder
  linarith only [he,hp0',hp',hg']

/-- Both sharp leading bounds hold uniformly over signed frequencies and allowed widths. -/
theorem eventually_joint_uniform_high_bounds (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) (hm : 0 < testMass f.1.1)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, ∀ (W : ℝ) (hW : 0 < W),
      jointSeedWidth κ L ≤ W → W ≤ 1 → ∀ T : ℝ, Real.exp (7*L/8) ≤ |T| →
      2*Real.log |T|-(2*(Real.log 2+10+Real.log 4)+1) ≤
        jointPairFullEnergy (jointDilatedTest f W hW) L T/(W*testMass f.1.1) ∧
      jointPairFullEnergy (jointDilatedTest f W hW) L T/(W*testMass f.1.1) ≤
        2*Real.log (1+|T|)+9 := by
  have herr := (tendsto_jointUniformUpperRemainder_zero f κ).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_joint_uniform_high_lower f hf hm hκ,herr,
    eventually_ge_atTop (3:ℝ)] with L hlo herr hL
  intro W hW hWlo hW1 T hT
  refine ⟨hlo W hW hWlo hW1 T hT,?_⟩
  have h := joint_uniform_high_upper f hf hm hκ (by linarith) hW hWlo hW1 hT
  have heq : jointPairFullEnergy (jointDilatedTest f W hW) L |T| =
      jointPairFullEnergy (jointDilatedTest f W hW) L T := by
    rcases le_total 0 T with hT0 | hT0
    · rw [abs_of_nonneg hT0]
    · rw [abs_of_nonpos hT0]
      exact jointPairFullEnergy_neg _ (jointDilatedProfile_support hf hW) hW (by linarith) T
  rw [heq] at h
  linarith only [h,herr]

/-- Concrete source capstone: no regularity, support, mass, or sign premise is supplied. -/
theorem eventually_jointUnitBump_uniform_high_bounds :
    ∀ᶠ L : ℝ in atTop, ∀ (W : ℝ) (hW : 0 < W),
      jointSeedWidth (jointSeedBalance jointUnitBumpTest) L ≤ W → W ≤ 1 →
      ∀ T : ℝ, Real.exp (7*L/8) ≤ |T| →
      2*Real.log |T|-(2*(Real.log 2+10+Real.log 4)+1) ≤
        jointPairFullEnergy (jointDilatedTest jointUnitBumpTest W hW) L T/
          (W*testMass jointUnitBumpTest.1.1) ∧
      jointPairFullEnergy (jointDilatedTest jointUnitBumpTest W hW) L T/
          (W*testMass jointUnitBumpTest.1.1) ≤ 2*Real.log (1+|T|)+9 :=
  eventually_joint_uniform_high_bounds jointUnitBumpTest jointUnitBumpTest_support
    jointUnitBumpTest_mass_pos (jointSeedBalance_pos jointUnitBumpTest
      jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero)

end RHTower.WeilWorkPBAP
