import GaloisForLFunctions.RHTower.WeilWorkPBAPJointBoundarySeed
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointUniformHigh

/-!
# The positive survivor of the logarithmic one-node boundary

Three frequency bands yield an explicit positive cosine certificate for the
actual unit bump when d > 1. Both signed poles remain in the energy.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem boundary_low_cos {L s T : ℝ} (hs : L-Real.log 2 ≤ s)
    (hT : |T| ≤ Real.exp (7*L/8)) :
    1-2*Real.exp (-L/4) ≤ Real.cos (Real.exp (-s)*T) := by
  have he := Real.exp_le_exp.mpr (show -s ≤ -L+Real.log 2 by linarith)
  rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] at he
  have hx : |Real.exp (-s)*T| ≤ 2*Real.exp (-L/8) := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.exp (-L)*2)*Real.exp (7*L/8) := by gcongr
      _ = _ := by
        rw [mul_right_comm,← Real.exp_add,show -L+7*L/8=-L/8 by ring]
        ring
  have hx2 := pow_le_pow_left₀ (abs_nonneg (Real.exp (-s)*T)) hx 2
  have hr : (2*Real.exp (-L/8))^2=4*Real.exp (-L/4) := by
    rw [mul_pow,← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-L/8)=-L/4 by ring]
  rw [sq_abs,hr] at hx2
  have hc := Real.one_sub_sq_div_two_le_cos (x:=Real.exp (-s)*T)
  nlinarith only [hx2,hc]

private theorem boundary_scalar_conditions {d : ℝ} (hd : 1 < d) (A B : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ s : ℝ, L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      0 < 2*s-(d-1)*Real.log L ∧ 2*s-(d-1)*Real.log L ≤ 5*L ∧
      0 ≤ (d-1)*Real.log L ∧ (d-1)*Real.log L ≤ L ∧
      A+1 ≤ (d-1)*Real.log L/2 ∧ B ≤ (d-1)*Real.log L/2 ∧ B ≤ L ∧
      10*L*Real.exp (-L/4) ≤ 1 := by
  have hr : 0 < d-1 := by linarith
  have hl : Tendsto (fun L : ℝ => (d-1)*(Real.log L/L)) atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℝ => Real.log L/L) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa only [mul_zero] using h.const_mul (d-1)
  have hh := hl.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (2*(|A|+|B|+1)/(d-1)))
  have he : Tendsto (fun L : ℝ => 10*L*Real.exp (-L/4)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/4) (by norm_num)).const_mul 10
    simp only [Real.rpow_one,mul_zero] at h
    convert h using 1
    funext L
    rw [show -(1/4:ℝ)*L=-L/4 by ring]
    ring
  have he1 := he.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hh,hlog,he1,eventually_ge_atTop (max B 3)] with L hh hlog he1 hL
  intro s hslo hshi
  have hL3 : 3 ≤ L := (le_max_right B 3).trans hL
  have hLp : 0 < L := by linarith
  have hB : B ≤ L := (le_max_left B 3).trans hL
  have hb : (d-1)*Real.log L ≤ L := by
    have h : (d-1)*Real.log L/L < 1 := by simpa only [mul_div_assoc] using hh
    have ht := (div_lt_iff₀ hLp).mp h
    linarith only [ht]
  have hb0 : 0 ≤ (d-1)*Real.log L := mul_nonneg hr.le (Real.log_nonneg (by linarith))
  have hbig := (div_le_iff₀ hr).mp hlog
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  refine ⟨by linarith only [hslo,hl2,hb,hL3],by linarith only [hshi,hl2,hb0,hL3],hb0,hb,
    ?_,?_,hB,he1.le⟩
  · linarith [le_abs_self A,abs_nonneg B]
  · linarith [le_abs_self B,abs_nonneg A]

/-- The explicit normalized cosine coefficient is positive and works at every real frequency. -/
theorem eventually_jointUnitBump_boundary_cosine_certificate {d : ℝ} (hd : 1 < d) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : ℝ), L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      ∀ hK : 0 < jointBoundaryScale d L s,
      let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
      let hW := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
        jointUnitBumpTest_integral_ne_zero L hK
      let g := jointDilatedTest jointUnitBumpTest W hW
      0 < 2*s-(d-1)*Real.log L ∧ ∀ T : ℝ,
        (d-1)*Real.log L/2 ≤ jointPairFullEnergy g L T/(W*testMass jointUnitBumpTest.1.1)+
          (2*s-(d-1)*Real.log L)*Real.cos (Real.exp (-s)*T) := by
  let A := jointBoundarySeedCost jointUnitBumpTest
  let B := 2*(Real.log 2+10+Real.log 4)+1
  have hw := eventually_jointBoundaryWidth_bounds jointUnitBumpTest
    jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero
  filter_upwards [eventually_jointUnitBump_boundary_seed_expansion d,
    eventually_jointUnitBump_uniform_high_bounds,eventually_jointBoundaryScale_bounds d,
    hw,boundary_scalar_conditions hd A B,eventually_ge_atTop (3:ℝ)]
    with L hseed hhigh hscale hw hscalar hL
  intro s hslo hshi hK
  let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
  have hW : 0 < W := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero L hK
  let g := jointDilatedTest jointUnitBumpTest W hW
  let a := 2*s-(d-1)*Real.log L
  let b := (d-1)*Real.log L
  have hm : 0 < W*testMass jointUnitBumpTest.1.1 := mul_pos hW jointUnitBumpTest_mass_pos
  obtain ⟨hKlo,hKhi⟩ := hscale s hslo hshi
  have hwK := hw _ hKlo hKhi
  obtain ⟨ha,ha5,hb0,hbL,hAb,hBb,hBL,hdec⟩ := hscalar s hslo hshi
  refine ⟨ha,?_⟩
  intro T
  change b/2 ≤ jointPairFullEnergy g L T/(W*testMass jointUnitBumpTest.1.1)+
    a*Real.cos (Real.exp (-s)*T)
  by_cases hT : |T| ≤ Real.exp (7*L/8)
  · have hc := boundary_low_cos hslo hT
    have hcd : ∀ y ∈ Icc 0 W, 0 ≤ (EF.weilTest g.1.1 g.1.1 y).re := by
      intro y _
      change 0 ≤ (EF.weilTest (jointDilatedProfile jointUnitBumpTest.1.1 W)
        (jointDilatedProfile jointUnitBumpTest.1.1 W) y).re
      rw [jointDilatedProfile_corr jointUnitBumpTest.1.1 hW]
      simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      exact mul_nonneg hW.le (jointUnitBumpTest_corr_nonneg _)
    have he0 := jointPairFullEnergy_zero_le g (L:=L)
      (jointDilatedProfile_support jointUnitBumpTest_support hW) hW hwK.2.2.1 hcd T
    have he := div_le_div_of_nonneg_right he0 hm.le
    have hs := (abs_le.mp (hseed s hslo hshi hK)).1
    change -A ≤ jointPairFullEnergy g L 0/(W*testMass jointUnitBumpTest.1.1)+2*s-2*(d-1)*Real.log L at hs
    have hc' := mul_le_mul_of_nonneg_left hc ha.le
    have hloss := mul_le_mul_of_nonneg_right ha5 (show 0 ≤ 2*Real.exp (-L/4) by positivity)
    change A+1 ≤ b/2 at hAb
    simp only [a,b] at hs hAb hc' hloss ⊢
    nlinarith only [he,hs,hc',hloss,hdec,hAb]
  · have ht := le_of_not_ge hT
    have he := (hhigh W hW hwK.2.2.2 hwK.2.1 T ht).1
    change 2*Real.log |T|-B ≤ jointPairFullEnergy g L T/(W*testMass jointUnitBumpTest.1.1) at he
    by_cases hphase : Real.exp (-s)*|T| ≤ Real.pi/2
    · have hc : 0 ≤ Real.cos (Real.exp (-s)*T) := by
        apply Real.cos_nonneg_of_mem_Icc
        apply abs_le.mp
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        exact hphase
      have hlog := Real.log_le_log (Real.exp_pos (7*L/8)) ht
      rw [Real.log_exp] at hlog
      have hcos := mul_nonneg ha.le hc
      change b ≤ L at hbL
      change 0 ≤ a*Real.cos (Real.exp (-s)*T) at hcos
      linarith only [he,hlog,hbL,hBL,hcos,hL]
    · have hphase' : 1 ≤ Real.exp (-s)*|T| := by
        have hp : 2 < Real.pi := by linarith [Real.pi_gt_three]
        linarith only [lt_of_not_ge hphase,hp]
      have hex : Real.exp s*Real.exp (-s)=1 := by
        rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
      have ht1 := mul_le_mul_of_nonneg_left hphase' (Real.exp_pos s).le
      rw [mul_one,← mul_assoc,hex,one_mul] at ht1
      have hlog := Real.log_le_log (Real.exp_pos s) ht1
      rw [Real.log_exp] at hlog
      have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (Real.exp (-s)*T)) ha.le
      change B ≤ b/2 at hBb
      dsimp only [a,b] at hBb hcos ⊢
      linarith only [he,hlog,hcos,hBb]

end RHTower.WeilWorkPBAP
