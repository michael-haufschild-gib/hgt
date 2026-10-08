import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedLimit

/-!
# Uniform high-frequency energy in the shrinking-width family

Every height above exp(7*L/8) satisfies the same actual full-energy lower bound.
Exact dilated mass and both signed poles are retained. Elementary exponential
errors tend to zero uniformly in height; no positivity producer is assumed.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- An elementary bound removes the logarithmic loss from the high-frequency remainder. -/
theorem joint_scaled_gamma_loss_le {W T D : ℝ} (hW : 0 < W) (hT : 2 ≤ T) :
    (Real.log (T/2)/(2*Real.pi))*(64*(D/W)^2/T^3) ≤
      (64*D^2/(2*Real.pi))/(W^2*T^2) := by
  have hTp : 0 < T := by linarith
  have hlog : Real.log (T/2) ≤ T :=
    (Real.log_le_sub_one_of_pos (by positivity : 0<T/2)).trans (by linarith)
  calc
    _ = (64*D^2/(2*Real.pi*W^2*T^3))*Real.log (T/2) := by ring
    _ ≤ (64*D^2/(2*Real.pi*W^2*T^3))*T :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by field_simp

/-- Both signed poles admit an elementary bound uniform in a small width. -/
theorem joint_scaled_pole_loss_le {W L T D : ℝ}
    (hW1 : W ≤ 1) (hL : 0 ≤ L) :
    4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
      (Real.exp (W/2)*(D/W)/T^2)^2 ≤
      16*Real.exp (L/2+1)*D^2/(W^2*T^4) := by
  have hplus : 1 ≤ Real.exp (L/2) := Real.one_le_exp_iff.mpr (by linarith)
  have hminus : Real.exp (-L/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hfactor : (1+Real.exp (L/2))*(1+Real.exp (-L/2)) ≤ 4*Real.exp (L/2) := by
    calc
      _ ≤ (2*Real.exp (L/2))*2 := by gcongr <;> linarith
      _ = _ := by ring
  have hwidth : (Real.exp (W/2))^2 ≤ Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  calc
    _ = 4*((1+Real.exp (L/2))*(1+Real.exp (-L/2)))*
        (Real.exp (W/2))^2*(D/W/T^2)^2 := by ring
    _ ≤ 4*(4*Real.exp (L/2))*Real.exp 1*(D/W/T^2)^2 := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

/-- Actual high-frequency pair energy with elementary width and height errors. -/
theorem joint_dilated_pair_high_simple (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) {W L T : ℝ}
    (hW : 0 < W) (hW1 : W ≤ 1) (hWL : W < L) (hT : 2 ≤ T) :
    2*W*testMass f.1.1*(Real.log (T/2)-(10+Real.log 4)) -
      (64*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(2*Real.pi))/(W^2*T^2) -
      16*Real.exp (L/2+1)*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(W^2*T^4) ≤
      jointPairFullEnergy (jointDilatedTest f W hW) L T := by
  have hL : 0 ≤ L := by linarith
  have h := joint_pair_full_energy_high_lower (jointDilatedTest f W hW)
    (jointDilatedProfile_support hf hW) hWL hL hT
  change 2*testMass (jointDilatedProfile f.1.1 W)*(Real.log (T/2)-(10+Real.log 4))-
    (Real.log (T/2)/(2*Real.pi))*
      (64*(∫u:ℝ,‖deriv (deriv (jointDilatedProfile f.1.1 W)) u‖)^2/T^3)-
    4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
      (Real.exp (W/2)*(∫u:ℝ,‖deriv (deriv (jointDilatedProfile f.1.1 W)) u‖)/T^2)^2 ≤ _ at h
  rw [jointDilatedProfile_mass f.1.1 hW,jointDilatedProfile_deriv_two_norm f.1.1 hW] at h
  have hg := joint_scaled_gamma_loss_le (D:=∫u:ℝ,‖deriv (deriv f.1.1) u‖) hW hT
  have hp := joint_scaled_pole_loss_le (T:=T) (D:=∫u:ℝ,‖deriv (deriv f.1.1) u‖)
    hW1 hL
  nlinarith

/-- Gamma leakage is exponentially small after the literal balanced-width normalization. -/
theorem joint_width_gamma_error_le {κ L T m C : ℝ}
    (hκ : 0 < κ) (hL : 1 ≤ L) (hm : 0 < m) (hC : 0 ≤ C)
    (hT : Real.exp (7*L/8) ≤ T) :
    (C/((jointSeedWidth κ L)^2*T^2))/(jointSeedWidth κ L*m*L) ≤
      (C/(κ^3*m))*Real.exp (-L/4) := by
  have hLp : 0 < L := by linarith
  have hW := jointSeedWidth_pos hκ hLp
  have hH : 0 < Real.exp (7*L/8) := Real.exp_pos _
  have hTp : 0 < T := hH.trans_le hT
  have he : (Real.exp (-L/2))^3*(Real.exp (7*L/8))^2*Real.exp (-L/4)=1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    norm_num
    ring
  have hi : 1/((jointSeedWidth κ L)^3*(Real.exp (7*L/8))^2*L)=
      Real.exp (-L/4)/(κ^3*L^4) := by
    unfold jointSeedWidth
    field_simp
    convert he.symm using 1; ring_nf
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  calc
    _ ≤ (C/((jointSeedWidth κ L)^2*(Real.exp (7*L/8))^2))/
        (jointSeedWidth κ L*m*L) := by gcongr
    _ = (C/m)*(1/((jointSeedWidth κ L)^3*(Real.exp (7*L/8))^2*L)) := by ring
    _ = (C/(κ^3*m))*(Real.exp (-L/4)/L^4) := by rw [hi]; ring
    _ ≤ (C/(κ^3*m))*Real.exp (-L/4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_self (Real.exp_pos _).le hL4

/-- Both pole losses are exponentially small in the same normalized high-frequency region. -/
theorem joint_width_pole_error_le {κ L T m C : ℝ}
    (hκ : 0 < κ) (hL : 1 ≤ L) (hm : 0 < m) (hC : 0 ≤ C)
    (hT : Real.exp (7*L/8) ≤ T) :
    (C*Real.exp (L/2)/((jointSeedWidth κ L)^2*T^4))/(jointSeedWidth κ L*m*L) ≤
      (C/(κ^3*m))*Real.exp (-3*L/2) := by
  have hLp : 0 < L := by linarith
  have hW := jointSeedWidth_pos hκ hLp
  have hH : 0 < Real.exp (7*L/8) := Real.exp_pos _
  have hTp : 0 < T := hH.trans_le hT
  have he : (Real.exp (-L/2))^3*(Real.exp (7*L/8))^4*Real.exp (-3*L/2)=
      Real.exp (L/2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have hi : Real.exp (L/2)/((jointSeedWidth κ L)^3*(Real.exp (7*L/8))^4*L)=
      Real.exp (-3*L/2)/(κ^3*L^4) := by
    unfold jointSeedWidth
    field_simp
    convert he.symm using 1; ring_nf
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  calc
    _ ≤ (C*Real.exp (L/2)/((jointSeedWidth κ L)^2*(Real.exp (7*L/8))^4))/
        (jointSeedWidth κ L*m*L) := by gcongr
    _ = (C/m)*(Real.exp (L/2)/((jointSeedWidth κ L)^3*(Real.exp (7*L/8))^4*L)) := by ring
    _ = (C/(κ^3*m))*(Real.exp (-3*L/2)/L^4) := by rw [hi]; ring
    _ ≤ (C/(κ^3*m))*Real.exp (-3*L/2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_self (Real.exp_pos _).le hL4

/-- Actual paired energy along the width family, including parameters outside the eventual region. -/
def jointSeedPairEnergy (f : JointSmoothTest) (κ L T : ℝ) : ℝ :=
  weilArchRe (EF.weilTest
    (clusterDifference (cosineProfile (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) T) L)
    (clusterDifference (cosineProfile (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) T) L))+
  weilArchRe (EF.weilTest
    (clusterDifference (sineProfile (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) T) L)
    (clusterDifference (sineProfile (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) T) L))

def jointWidthGammaCost (f : JointSmoothTest) (κ : ℝ) : ℝ :=
  (64*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(2*Real.pi))/(κ^3*testMass f.1.1)

def jointWidthPoleCost (f : JointSmoothTest) (κ : ℝ) : ℝ :=
  (16*Real.exp 1*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2)/(κ^3*testMass f.1.1)

def jointWidthHighError (f : JointSmoothTest) (κ L : ℝ) : ℝ :=
  2*(Real.log 2+10+Real.log 4)/L+
    jointWidthGammaCost f κ*Real.exp (-L/4)+
    jointWidthPoleCost f κ*Real.exp (-3*L/2)

/-- Uniform normalized lower bound throughout the positive high-frequency region. -/
theorem joint_seed_pair_high_normalized_lower (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) (hm : 0 < testMass f.1.1)
    {κ L T : ℝ} (hκ : 0 < κ) (hL : 2 ≤ L)
    (hW1 : jointSeedWidth κ L ≤ 1) (hT : Real.exp (7*L/8) ≤ T) :
    7/4-jointWidthHighError f κ L ≤
      jointSeedPairEnergy f κ L T/(jointSeedWidth κ L*testMass f.1.1*L) := by
  have hLp : 0 < L := by linarith
  have hW := jointSeedWidth_pos hκ hLp
  have hWL : jointSeedWidth κ L < L := by linarith
  have hTp : 0 < T := (Real.exp_pos _).trans_le hT
  have hT2 : 2 ≤ T := by linarith [Real.add_one_le_exp (7*L/8)]
  have hd : 0 < jointSeedWidth κ L*testMass f.1.1*L := mul_pos (mul_pos hW hm) hLp
  have h := joint_dilated_pair_high_simple f hf hW hW1 hWL hT2
  change 2*jointSeedWidth κ L*testMass f.1.1*(Real.log (T/2)-(10+Real.log 4)) -
      (64*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(2*Real.pi))/((jointSeedWidth κ L)^2*T^2) -
      16*Real.exp (L/2+1)*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/((jointSeedWidth κ L)^2*T^4) ≤
      jointSeedPairEnergy f κ L T at h
  have he := div_le_div_of_nonneg_right h hd.le
  rw [sub_div,sub_div] at he
  have hg := joint_width_gamma_error_le (C:=64*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/(2*Real.pi))
    hκ (by linarith : 1≤L) hm (by positivity) hT
  have hp := joint_width_pole_error_le (C:=16*Real.exp 1*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2)
    hκ (by linarith : 1≤L) hm (by positivity) hT
  have hp' :
      (16*Real.exp (L/2+1)*(∫u:ℝ,‖deriv (deriv f.1.1) u‖)^2/((jointSeedWidth κ L)^2*T^4))/
        (jointSeedWidth κ L*testMass f.1.1*L) ≤ jointWidthPoleCost f κ*Real.exp (-3*L/2) := by
    unfold jointWidthPoleCost
    convert hp using 1
    rw [Real.exp_add]
    ring
  have hlog := Real.log_le_log (Real.exp_pos (7*L/8)) hT
  rw [Real.log_exp] at hlog
  have hl : 7*L/8-Real.log 2 ≤ Real.log (T/2) := by
    rw [Real.log_div hTp.ne' (by norm_num : (2:ℝ)≠0)]
    linarith
  have hmain : 7/4-2*(Real.log 2+10+Real.log 4)/L ≤
      (2*jointSeedWidth κ L*testMass f.1.1*(Real.log (T/2)-(10+Real.log 4)))/
        (jointSeedWidth κ L*testMass f.1.1*L) := by
    calc
      _ = 2*(7*L/8-Real.log 2-(10+Real.log 4))/L := by field_simp; ring
      _ ≤ 2*(Real.log (T/2)-(10+Real.log 4))/L := by gcongr
      _ = _ := by field_simp
  change _ ≤ jointWidthGammaCost f κ*Real.exp (-L/4) at hg
  unfold jointWidthHighError
  linarith

private theorem tendsto_exp_neg_coeff {b : ℝ} (hb : 0 < b) :
    Tendsto (fun L : ℝ => Real.exp (-b*L)) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero,one_mul] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb

/-- All error constants are literal source costs; their normalized error tends to zero. -/
theorem tendsto_jointWidthHighError_zero (f : JointSmoothTest) (κ : ℝ) :
    Tendsto (jointWidthHighError f κ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℝ => Real.exp (-L/4)) atTop (𝓝 0) := by
    convert tendsto_exp_neg_coeff (by norm_num : (0:ℝ)<1/4) using 1
    funext L
    congr 1
    ring
  have h2 : Tendsto (fun L : ℝ => Real.exp (-3*L/2)) atTop (𝓝 0) := by
    convert tendsto_exp_neg_coeff (by norm_num : (0:ℝ)<3/2) using 1
    funext L
    congr 1
    ring
  have h0 : Tendsto (fun L : ℝ => 2*(Real.log 2+10+Real.log 4)/L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop _
  have ht := (h0.add (h1.const_mul (jointWidthGammaCost f κ))).add
    (h2.const_mul (jointWidthPoleCost f κ))
  change Tendsto (fun L => jointWidthHighError f κ L) atTop (𝓝 0)
  simpa only [jointWidthHighError,mul_zero,add_zero] using ht

/-- One eventual threshold controls every signed height in the expanding high-frequency region. -/
theorem eventually_jointSeedPairEnergy_high (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) (hm : 0 < testMass f.1.1)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, ∀ T : ℝ, Real.exp (7*L/8) ≤ |T| →
      (13/8:ℝ)*(jointSeedWidth κ L*testMass f.1.1*L) ≤ jointSeedPairEnergy f κ L T := by
  have herr := (tendsto_jointWidthHighError_zero f κ).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/8))
  filter_upwards [herr,eventually_jointSeedWidth_small κ,eventually_ge_atTop (3:ℝ)]
    with L herr hWs hL
  intro T hT
  have hLp : 0 < L := by linarith
  have hW := jointSeedWidth_pos hκ hLp
  have hd : 0 < jointSeedWidth κ L*testMass f.1.1*L := mul_pos (mul_pos hW hm) hLp
  have h := joint_seed_pair_high_normalized_lower f hf hm hκ (by linarith) hWs.1 hT
  have heq : jointSeedPairEnergy f κ L |T|=jointSeedPairEnergy f κ L T := by
    rcases le_total 0 T with hT0 | hT0
    · rw [abs_of_nonneg hT0]
    · rw [abs_of_nonpos hT0]
      change jointPairFullEnergy (jointDilatedTest f (jointSeedWidth κ L) hW) L (-T)=
        jointPairFullEnergy (jointDilatedTest f (jointSeedWidth κ L) hW) L T
      exact jointPairFullEnergy_neg _ (jointDilatedProfile_support hf hW) hW (by linarith) T
  rw [heq] at h
  have hmul := (le_div_iff₀ hd).mp h
  nlinarith

end RHTower.WeilWorkPBAP
