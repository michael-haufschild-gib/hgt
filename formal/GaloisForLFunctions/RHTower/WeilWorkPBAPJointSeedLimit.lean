import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedGamma
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedPole
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual negative seed at the balanced shrinking width

For width kappa * L * exp(-L/2), the literal full seed divided by width * L
tends to baseMass - 2*kappa*norm(sourceIntegral)^2. The source-defined balanced
coefficient gives normalized limit -1 and eventual negative full energy.
Support and nondegeneracy are source conditions; no energy-sign or positivity
producer is assumed. Both signed poles remain in the functional.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

def jointSeedWidth (κ L : ℝ) : ℝ := κ*L*Real.exp (-L/2)

theorem jointSeedWidth_pos {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L) :
    0 < jointSeedWidth κ L := by unfold jointSeedWidth; positivity

theorem tendsto_jointSeedWidth_zero (κ : ℝ) :
    Tendsto (jointSeedWidth κ) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/2) (by norm_num)
  have he : (fun L : ℝ => L*Real.exp (-L/2)) =
      (fun L : ℝ => L^(1:ℝ)*Real.exp (-(1/2)*L)) := by
    funext L
    rw [Real.rpow_one]
    congr 2; ring
  have ht0 : Tendsto (fun L : ℝ => L*Real.exp (-L/2)) atTop (𝓝 0) := by
    rw [he]
    exact h
  have ht := ht0.const_mul κ
  change Tendsto (fun L : ℝ => κ*L*Real.exp (-L/2)) atTop (𝓝 0)
  simpa only [mul_zero, mul_assoc] using ht

theorem tendsto_jointSeedWidth_log_div {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L => Real.log (jointSeedWidth κ L)/L) atTop (𝓝 (-(1/2:ℝ))) := by
  have hlog : Tendsto (fun L : ℝ => Real.log L/L) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hc : Tendsto (fun L : ℝ => Real.log κ/L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (Real.log κ)
  have ht := (hc.add hlog).sub_const (1/2:ℝ)
  simp only [add_zero, zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [jointSeedWidth, Real.log_mul (mul_pos hκ hL).ne' (Real.exp_pos _).ne',
    Real.log_mul hκ.ne' hL.ne', Real.log_exp]
  field_simp
  ring

theorem eventually_jointSeedWidth_small (κ : ℝ) :
    ∀ᶠ L : ℝ in atTop, jointSeedWidth κ L ≤ 1 ∧ jointSeedWidth κ L < L := by
  have hW := (tendsto_jointSeedWidth_zero κ).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hW,eventually_gt_atTop (1:ℝ)] with L hW hL
  exact ⟨hW.le,hW.trans hL⟩

theorem joint_seed_pole_normalized_eq (f : JointSmoothTest) {κ L : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) :
    testPole (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L) /
      (jointSeedWidth κ L*L) =
        -κ*(1-Real.exp (-L/2))^2*jointSeedPoleProfile f (jointSeedWidth κ L) := by
  rw [joint_seed_pole_eq f (jointSeedWidth_pos hκ hL)]
  have he : Real.exp (L/2)*Real.exp (-L/2)=1 := by
    rw [← Real.exp_add, show L/2+-L/2=0 by ring, Real.exp_zero]
  have hc : 2*(Real.cosh (L/2)-1)*Real.exp (-L/2)=(1-Real.exp (-L/2))^2 := by
    rw [Real.cosh_eq, show -(L/2) = -L/2 by ring]
    nlinarith
  calc
    _ = -κ*jointSeedPoleProfile f (jointSeedWidth κ L)*
        (2*(Real.cosh (L/2)-1)*Real.exp (-L/2)) := by
      set q := jointSeedPoleProfile f (jointSeedWidth κ L)
      change -2*(Real.cosh (L/2)-1)*(κ*L*Real.exp (-L/2))^2*q /
        ((κ*L*Real.exp (-L/2))*L) = -κ*q*(2*(Real.cosh (L/2)-1)*Real.exp (-L/2))
      field_simp
    _ = _ := by rw [hc]; ring

theorem tendsto_joint_seed_pole_normalized (f : JointSmoothTest) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L =>
      testPole (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L) /
        (jointSeedWidth κ L*L)) atTop (𝓝 (-2*κ*‖∫ u : ℝ, f.1.1 u‖^2)) := by
  have he : Tendsto (fun L : ℝ => Real.exp (-L/2)) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1/2) (by norm_num)
    have heq : (fun L : ℝ => Real.exp (-L/2)) =
        (fun L : ℝ => L^(0:ℝ)*Real.exp (-(1/2)*L)) := by
      funext L
      rw [Real.rpow_zero, one_mul]
      congr 1; ring
    rwa [heq]
  have hq := (tendsto_jointSeedPoleProfile_zero f).comp (tendsto_jointSeedWidth_zero κ)
  have h1 : Tendsto (fun L : ℝ => 1-Real.exp (-L/2)) atTop (𝓝 (1-0:ℝ)) :=
    tendsto_const_nhds.sub he
  have ht := ((h1.pow 2).const_mul (-κ)).mul hq
  have hv : -κ*((1:ℝ)-0)^2*(2*‖∫u:ℝ,f.1.1 u‖^2) = -2*κ*‖∫u:ℝ,f.1.1 u‖^2 := by ring
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact (joint_seed_pole_normalized_eq f hκ hL).symm

/-- The actual seed Gamma term, divided by width times separation, has limit mass. -/
theorem tendsto_joint_seed_gamma_normalized (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L =>
      testGamma (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L) /
        (jointSeedWidth κ L*L)) atTop (𝓝 (testMass f.1.1)) := by
  let r (L : ℝ) :=
    testGamma (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L) /
      (jointSeedWidth κ L*L) + 2*testMass f.1.1*(Real.log (jointSeedWidth κ L)/L)
  have hb : ∀ᶠ L : ℝ in atTop, |r L| ≤ jointSeedLogCost f/L := by
    filter_upwards [eventually_gt_atTop (0:ℝ),eventually_jointSeedWidth_small κ]
      with L hL hWs
    have hW := jointSeedWidth_pos hκ hL
    have h := joint_cluster_gamma_scale_mass_bound f hf hW hWs.1 hWs.2
    calc
      |r L| = |testGamma (clusterDifference
          (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L) +
          2*jointSeedWidth κ L*testMass f.1.1*Real.log (jointSeedWidth κ L)| /
          (jointSeedWidth κ L*L) := by
        rw [← abs_of_pos (mul_pos hW hL), ← abs_div]
        congr 1
        dsimp [r]
        field_simp
      _ ≤ (jointSeedWidth κ L*jointSeedLogCost f)/(jointSeedWidth κ L*L) :=
        div_le_div_of_nonneg_right h (mul_pos hW hL).le
      _ = jointSeedLogCost f/L := by field_simp
  have hr : Tendsto r atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg (r L)))
      (hb.mono (fun L h => by simpa only [Real.norm_eq_abs] using h))
    exact tendsto_id.const_div_atTop (jointSeedLogCost f)
  have hm := (tendsto_jointSeedWidth_log_div hκ).const_mul (2*testMass f.1.1)
  have ht := hr.sub hm
  have hc : 0-2*testMass f.1.1*(-(1/2:ℝ))=testMass f.1.1 := by ring
  rw [hc] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun L => by dsimp [r]; ring)

/-- Literal full seed energy, defined for every separation. -/
def jointSeedFullEnergy (f : JointSmoothTest) (κ L : ℝ) : ℝ :=
  weilArchRe (EF.weilTest
    (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L)
    (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L))

/-- The signed poles and exact Gamma coefficient give the actual seed limit. -/
theorem tendsto_jointSeedFullEnergy_normalized (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L => jointSeedFullEnergy f κ L/(jointSeedWidth κ L*L)) atTop
      (𝓝 (testMass f.1.1-2*κ*‖∫u:ℝ,f.1.1 u‖^2)) := by
  have ht := (tendsto_joint_seed_pole_normalized f hκ).add
    (tendsto_joint_seed_gamma_normalized f hf hκ)
  have hc : -2*κ*‖∫u:ℝ,f.1.1 u‖^2+testMass f.1.1 =
      testMass f.1.1-2*κ*‖∫u:ℝ,f.1.1 u‖^2 := by ring
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hp := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (jointDilatedTest f (jointSeedWidth κ L)
      (jointSeedWidth_pos hκ hL)) L).1
  change jointSeedFullEnergy f κ L =
    testPole (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L)+
    testGamma (clusterDifference (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) L) at hp
  rw [hp, add_div]

/-- A source-defined coefficient balances the Gamma scale against the two poles. -/
def jointSeedBalance (f : JointSmoothTest) : ℝ :=
  testMass f.1.1/‖∫u:ℝ,f.1.1 u‖^2

theorem jointSeedBalance_pos (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0) :
    0 < jointSeedBalance f := by
  exact div_pos hm (sq_pos_of_pos (norm_pos_iff.mpr hB))

/-- The balanced actual seed has negative normalized limit, with no energy premise. -/
theorem tendsto_jointSeedFullEnergy_balanced (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0) :
    Tendsto (fun L => jointSeedFullEnergy f (jointSeedBalance f) L /
      (jointSeedWidth (jointSeedBalance f) L*testMass f.1.1*L)) atTop (𝓝 (-1:ℝ)) := by
  have ht := (tendsto_jointSeedFullEnergy_normalized f hf (jointSeedBalance_pos f hm hB)).div_const
    (testMass f.1.1)
  have hnorm : ‖∫u:ℝ,f.1.1 u‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hB)
  have hc : (testMass f.1.1-2*jointSeedBalance f*‖∫u:ℝ,f.1.1 u‖^2)/testMass f.1.1 = -1 := by
    unfold jointSeedBalance
    field_simp
    ring
  rw [hc] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun L => by ring)

/-- Actual seed negativity and the quantitative lower bound needed by the phase certificate. -/
theorem eventually_jointSeedFullEnergy_balanced_bounds (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0) :
    ∀ᶠ L : ℝ in atTop,
      -(9/8:ℝ)*(jointSeedWidth (jointSeedBalance f) L*testMass f.1.1*L) ≤
        jointSeedFullEnergy f (jointSeedBalance f) L ∧
      jointSeedFullEnergy f (jointSeedBalance f) L < 0 := by
  have ht := tendsto_jointSeedFullEnergy_balanced f hf hm hB
  have hlo := ht.eventually (lt_mem_nhds (by norm_num : -(9/8:ℝ)< -1))
  have hup := ht.eventually (gt_mem_nhds (by norm_num : (-1:ℝ)<0))
  filter_upwards [hlo,hup,eventually_gt_atTop (0:ℝ)] with L hlo hup hL
  have hd : 0 < jointSeedWidth (jointSeedBalance f) L*testMass f.1.1*L :=
    mul_pos (mul_pos (jointSeedWidth_pos (jointSeedBalance_pos f hm hB) hL) hm) hL
  exact ⟨((lt_div_iff₀ hd).mp hlo).le,by simpa only [zero_mul] using (div_lt_iff₀ hd).mp hup⟩

end RHTower.WeilWorkPBAP
