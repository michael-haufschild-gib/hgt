import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedExpansion
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointPrimeLag

/-!
# Uniform seed energy at the one-node logarithmic boundary

The source-defined balance is used at variable scale K. Uniform error control
for L <= K <= 3L retains the logarithmic correction that decides the boundary.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Width with the actual source balance and independently varying scale. -/
def jointBoundaryWidth (f : JointSmoothTest) (L K : ℝ) : ℝ :=
  jointSeedBalance f*K*Real.exp (-L/2)

theorem jointBoundaryWidth_pos (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0)
    (L : ℝ) {K : ℝ} (hK : 0 < K) : 0 < jointBoundaryWidth f L K := by
  unfold jointBoundaryWidth
  exact mul_pos (mul_pos (jointSeedBalance_pos f hm hB) hK) (Real.exp_pos _)

private theorem boundary_cosh_exp {L : ℝ} (hL : 0 ≤ L) :
    Real.cosh (L/2)-1 ≤ Real.exp (L/2) := by
  rw [Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -(L/2) ≤ L/2 by linarith)
  linarith only [h]

private theorem boundary_pole_remainder (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0)
    {L K : ℝ} (hL : 0 < L) (hK : 0 < K) (hK3 : K ≤ 3*L) :
    (Real.cosh (L/2)-1)*(jointBoundaryWidth f L K)^3 /
      jointSeedBalance f ≤ 27*(jointSeedBalance f)^2*L^3*Real.exp (-L) := by
  have hκ := jointSeedBalance_pos f hm hB
  have hW := jointBoundaryWidth_pos f hm hB L hK
  have he : Real.exp (L/2)*(Real.exp (-L/2))^3=Real.exp (-L) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    norm_num
    ring
  calc
    _ ≤ Real.exp (L/2)*(jointBoundaryWidth f L K)^3/jointSeedBalance f := by
      gcongr
      exact boundary_cosh_exp hL.le
    _ = (jointSeedBalance f)^2*K^3*Real.exp (-L) := by
      unfold jointBoundaryWidth
      rw [mul_pow,mul_pow]
      rw [show Real.exp (L/2)*((jointSeedBalance f)^3*K^3*(Real.exp (-L/2))^3) =
        (jointSeedBalance f)^3*K^3*(Real.exp (L/2)*(Real.exp (-L/2))^3) by ring,he]
      field_simp
    _ ≤ (jointSeedBalance f)^2*(3*L)^3*Real.exp (-L) := by gcongr
    _ = _ := by ring

private theorem boundary_pole_center (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0)
    {L K : ℝ} (hK : 0 < K) :
    4*(Real.cosh (L/2)-1)*(jointBoundaryWidth f L K)^2*‖∫u:ℝ,f.1.1 u‖^2 /
      (jointBoundaryWidth f L K*testMass f.1.1) = 2*K*(1-Real.exp (-L/2))^2 := by
  have hκ := jointSeedBalance_pos f hm hB
  have hW := jointBoundaryWidth_pos f hm hB L hK
  have hBn : ‖∫u:ℝ,f.1.1 u‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hB)
  have he : Real.exp (L/2)*Real.exp (-L/2)=1 := by
    rw [← Real.exp_add,show L/2+-L/2=0 by ring,Real.exp_zero]
  have hc : 2*(Real.cosh (L/2)-1)*Real.exp (-L/2)=(1-Real.exp (-L/2))^2 := by
    rw [Real.cosh_eq,show -(L/2)=-L/2 by ring]
    nlinarith only [he]
  calc
    _ = 2*K*(2*(Real.cosh (L/2)-1)*Real.exp (-L/2)) := by
      unfold jointBoundaryWidth jointSeedBalance
      field_simp
      ring
    _ = _ := by rw [hc]

/-- Full normalized seed error, uniformly through a threefold range of scales. -/
theorem joint_boundary_seed_error (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0)
    {L K : ℝ} (hL : 0 < L) (hK : 0 < K) (hK3 : K ≤ 3*L)
    (hW1 : jointBoundaryWidth f L K ≤ 1) (hWL : jointBoundaryWidth f L K < L) :
    let W := jointBoundaryWidth f L K
    let hW := jointBoundaryWidth_pos f hm hB L hK
    |jointPairFullEnergy (jointDilatedTest f W hW) L 0/(W*testMass f.1.1)+
      2*Real.log W+2*K| ≤ jointSeedLogCost f/testMass f.1.1+
        27*(jointSeedBalance f)^2*L^3*Real.exp (-L)+12*L*Real.exp (-L/2) := by
  let W := jointBoundaryWidth f L K
  have hW : 0 < W := jointBoundaryWidth_pos f hm hB L hK
  have hκ := jointSeedBalance_pos f hm hB
  have hd : 0 < W*testMass f.1.1 := mul_pos hW hm
  have h := div_le_div_of_nonneg_right (joint_seed_full_expansion f hf hq hW hW1 hWL) hd.le
  rw [← abs_of_pos hd,← abs_div] at h
  have hnorm : (jointPairFullEnergy (jointDilatedTest f W hW) L 0+
      2*W*testMass f.1.1*Real.log W+4*(Real.cosh (L/2)-1)*W^2*‖∫u:ℝ,f.1.1 u‖^2)/
      (W*testMass f.1.1) =
      jointPairFullEnergy (jointDilatedTest f W hW) L 0/(W*testMass f.1.1)+
      2*Real.log W+2*K*(1-Real.exp (-L/2))^2 := by
    rw [add_div,add_div,boundary_pole_center f hm hB hK]
    congr 1
    field_simp
  have hright : (W*jointSeedLogCost f+(Real.cosh (L/2)-1)*W^4*‖∫u:ℝ,f.1.1 u‖^2)/
      (W*testMass f.1.1) = jointSeedLogCost f/testMass f.1.1+
      (Real.cosh (L/2)-1)*W^3/jointSeedBalance f := by
    unfold jointSeedBalance
    field_simp
  rw [abs_of_pos hd,hnorm,hright] at h
  have hp := boundary_pole_remainder f hm hB hL hK hK3
  have hq0 := (Real.exp_pos (-L/2)).le
  have hq1 : Real.exp (-L/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs : 0 ≤ 2*Real.exp (-L/2)-(Real.exp (-L/2))^2 := by nlinarith
  have hc : |2*K-2*K*(1-Real.exp (-L/2))^2| ≤ 12*L*Real.exp (-L/2) := by
    rw [abs_of_nonneg (by nlinarith only [mul_nonneg hK.le hs])]
    have hx := mul_le_mul_of_nonneg_right hK3 hq0
    nlinarith only [hx,mul_nonneg hK.le (sq_nonneg (Real.exp (-L/2)))]
  dsimp only
  calc
    _ = |(jointPairFullEnergy (jointDilatedTest f W hW) L 0/(W*testMass f.1.1)+
      2*Real.log W+2*K*(1-Real.exp (-L/2))^2)+(2*K-2*K*(1-Real.exp (-L/2))^2)| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (h.trans (by linarith only [hp])) hc)

/-- All widths in the scale interval are positive, small, and separated. -/
theorem eventually_jointBoundaryWidth_bounds (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0) :
    ∀ᶠ L : ℝ in atTop, ∀ K : ℝ, L ≤ K → K ≤ 3*L →
      0 < jointBoundaryWidth f L K ∧ jointBoundaryWidth f L K ≤ 1 ∧
      2*jointBoundaryWidth f L K < L ∧
      jointSeedWidth (jointSeedBalance f) L ≤ jointBoundaryWidth f L K := by
  have hκ := jointSeedBalance_pos f hm hB
  filter_upwards [eventually_jointSeedWidth_small (3*jointSeedBalance f),
    eventually_ge_atTop (3:ℝ)] with L hs hL
  intro K hKlo hKhi
  have hK : 0 < K := by linarith
  have hW1 : jointBoundaryWidth f L K ≤ 1 := by
    apply le_trans _ hs.1
    dsimp only [jointBoundaryWidth,jointSeedWidth]
    nlinarith only [mul_le_mul_of_nonneg_left hKhi
      (mul_pos hκ (Real.exp_pos (-L/2))).le]
  refine ⟨jointBoundaryWidth_pos f hm hB L hK,hW1,by linarith,?_⟩
  unfold jointBoundaryWidth jointSeedWidth
  gcongr

/-- The variable-scale seed has a bounded normalized remainder, uniform in scale. -/
theorem eventually_joint_boundary_seed_error (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0) :
    ∀ᶠ L : ℝ in atTop, ∀ (K : ℝ) (hK : 0 < K), L ≤ K → K ≤ 3*L →
      let W := jointBoundaryWidth f L K
      let hW := jointBoundaryWidth_pos f hm hB L hK
      |jointPairFullEnergy (jointDilatedTest f W hW) L 0/(W*testMass f.1.1)+
        2*Real.log W+2*K| ≤ jointSeedLogCost f/testMass f.1.1+2 := by
  have hp : Tendsto (fun L : ℝ => 27*(jointSeedBalance f)^2*L^3*Real.exp (-L)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 1 (by norm_num)).const_mul
      (27*(jointSeedBalance f)^2)
    simpa only [Real.rpow_ofNat,mul_zero,neg_one_mul,mul_assoc] using ht
  have hc : Tendsto (fun L : ℝ => 12*L*Real.exp (-L/2)) atTop (𝓝 0) := by
    exact tendsto_jointSeedWidth_zero 12
  have hp1 := hp.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hc1 := hc.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hp1,hc1,eventually_jointBoundaryWidth_bounds f hm hB,
    eventually_gt_atTop (0:ℝ)] with L hp1 hc1 hw hL
  intro K hK hlo hhi
  have hwK := hw K hlo hhi
  have h := joint_boundary_seed_error f hf hq hm hB hL hK hhi hwK.2.1 (by linarith [hwK.2.2.1])
  dsimp only at h ⊢
  linarith only [h,hp1,hc1]

/-- Exact scale at the logarithmic one-node boundary. -/
def jointBoundaryScale (d L s : ℝ) : ℝ := L/2+s-d*Real.log L

/-- The actual prime-lag range lies in one uniform scale interval. -/
theorem eventually_jointBoundaryScale_bounds (d : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ s : ℝ, L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      L ≤ jointBoundaryScale d L s ∧ jointBoundaryScale d L s ≤ 3*L := by
  have hl : Tendsto (fun L : ℝ => Real.log L/L) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have ht : Tendsto (fun L : ℝ => (|d| * Real.log L+Real.log 2)/L) atTop (𝓝 0) := by
    have hh := (hl.const_mul |d|).add (tendsto_id.const_div_atTop (Real.log 2))
    simp only [mul_zero,add_zero] at hh
    convert hh using 1
    funext L
    dsimp only [id]
    ring
  have hs := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with L hs hL
  intro s hslo hshi
  have hLp : 0 < L := by linarith
  have hb := (div_lt_iff₀ hLp).mp hs
  have hlog := Real.log_nonneg hL
  have hdlo := mul_le_mul_of_nonneg_right (neg_abs_le d) hlog
  have hdhi := mul_le_mul_of_nonneg_right (le_abs_self d) hlog
  unfold jointBoundaryScale
  constructor <;> linarith only [hb,hslo,hshi,hdlo,hdhi]

private theorem boundary_log_center (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0)
    {d L s : ℝ} (hL : 0 < L) (hK : 0 < jointBoundaryScale d L s) :
    2*Real.log (jointBoundaryWidth f L (jointBoundaryScale d L s))+
      2*jointBoundaryScale d L s =
      2*s-2*(d-1)*Real.log L+
        2*Real.log (jointSeedBalance f*jointBoundaryScale d L s/L) := by
  have hκ := jointSeedBalance_pos f hm hB
  rw [jointBoundaryWidth,Real.log_mul (mul_pos hκ hK).ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_div (mul_pos hκ hK).ne' hL.ne']
  unfold jointBoundaryScale
  ring

private theorem boundary_log_bounded {κ L K : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hKlo : L ≤ K) (hKhi : K ≤ 3*L) :
    |Real.log (κ*K/L)| ≤ |Real.log κ|+|Real.log (3*κ)| := by
  have hlo : κ ≤ κ*K/L := by
    apply (le_div_iff₀ hL).mpr
    exact mul_le_mul_of_nonneg_left hKlo hκ.le
  have hhi : κ*K/L ≤ 3*κ := by
    apply (div_le_iff₀ hL).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hKhi hκ.le]
  have hloglo := Real.log_le_log hκ hlo
  have hloghi := Real.log_le_log (hκ.trans_le hlo) hhi
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log κ),le_abs_self (Real.log (3*κ)),
    abs_nonneg (Real.log κ),abs_nonneg (Real.log (3*κ))]

/-- Source-defined constant for the logarithmic boundary expansion. -/
def jointBoundarySeedCost (f : JointSmoothTest) : ℝ :=
  jointSeedLogCost f/testMass f.1.1+2+
    2*(|Real.log (jointSeedBalance f)|+|Real.log (3*jointSeedBalance f)|)

/-- The exact logarithmic correction has uniformly bounded error over the entire lag range. -/
theorem eventually_joint_boundary_seed_expansion (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1)
    (hq : ∀ u : ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 u).re)
    (hm : 0 < testMass f.1.1) (hB : (∫u:ℝ,f.1.1 u) ≠ 0) (d : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : ℝ), L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      ∀ hK : 0 < jointBoundaryScale d L s,
      let W := jointBoundaryWidth f L (jointBoundaryScale d L s)
      let hW := jointBoundaryWidth_pos f hm hB L hK
      |jointPairFullEnergy (jointDilatedTest f W hW) L 0/(W*testMass f.1.1)+
        2*s-2*(d-1)*Real.log L| ≤ jointBoundarySeedCost f := by
  filter_upwards [eventually_joint_boundary_seed_error f hf hq hm hB,
    eventually_jointBoundaryScale_bounds d,eventually_gt_atTop (0:ℝ)] with L he hs hL
  intro s hslo hshi hK
  obtain ⟨hKlo,hKhi⟩ := hs s hslo hshi
  have heK := he (jointBoundaryScale d L s) hK hKlo hKhi
  have hlog := boundary_log_bounded (jointSeedBalance_pos f hm hB) hL hKlo hKhi
  have hc := boundary_log_center f hm hB hL hK
  dsimp only at heK ⊢
  calc
    _ = |(jointPairFullEnergy
        (jointDilatedTest f (jointBoundaryWidth f L (jointBoundaryScale d L s))
          (jointBoundaryWidth_pos f hm hB L hK)) L 0/
          (jointBoundaryWidth f L (jointBoundaryScale d L s)*testMass f.1.1)+
        2*Real.log (jointBoundaryWidth f L (jointBoundaryScale d L s))+
          2*jointBoundaryScale d L s)-2*Real.log (jointSeedBalance f*jointBoundaryScale d L s/L)| := by
      congr 1
      linarith only [hc]
    _ ≤ _ := by
      have ha := abs_add_le
        (jointPairFullEnergy
          (jointDilatedTest f (jointBoundaryWidth f L (jointBoundaryScale d L s))
            (jointBoundaryWidth_pos f hm hB L hK)) L 0/
            (jointBoundaryWidth f L (jointBoundaryScale d L s)*testMass f.1.1)+
          2*Real.log (jointBoundaryWidth f L (jointBoundaryScale d L s))+
            2*jointBoundaryScale d L s)
        (-(2*Real.log (jointSeedBalance f*jointBoundaryScale d L s/L)))
      rw [← sub_eq_add_neg,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
      unfold jointBoundarySeedCost
      linarith only [ha,heK,hlog]

/-- Literal unit-bump expansion: source support, mass, and correlation signs are paid. -/
theorem eventually_jointUnitBump_boundary_seed_expansion (d : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : ℝ), L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      ∀ hK : 0 < jointBoundaryScale d L s,
      let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
      let hW := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
        jointUnitBumpTest_integral_ne_zero L hK
      |jointPairFullEnergy (jointDilatedTest jointUnitBumpTest W hW) L 0/
          (W*testMass jointUnitBumpTest.1.1)+2*s-2*(d-1)*Real.log L| ≤
        jointBoundarySeedCost jointUnitBumpTest :=
  eventually_joint_boundary_seed_expansion jointUnitBumpTest jointUnitBumpTest_support
    jointUnitBumpTest_corr_nonneg jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero d

/-- Actual primes satisfy the full uniform expansion and width geometry. -/
theorem exists_jointUnitBump_prime_boundary_seed_expansion (d : ℝ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ p : Nat.Primes, L₀ ≤ Real.log (p:ℕ)/2 →
      let L := Real.log (p:ℕ)/2
      let s := Real.log (1/|jointIntegerLag L|)
      ∃ hK : 0 < jointBoundaryScale d L s,
      let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
      let hW := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
        jointUnitBumpTest_integral_ne_zero L hK
      W ≤ 1 ∧ 2*W < L ∧
      |jointPairFullEnergy (jointDilatedTest jointUnitBumpTest W hW) L 0/
          (W*testMass jointUnitBumpTest.1.1)+2*s-2*(d-1)*Real.log L| ≤
        jointBoundarySeedCost jointUnitBumpTest := by
  have hw := eventually_jointBoundaryWidth_bounds jointUnitBumpTest
    jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    (((eventually_jointUnitBump_boundary_seed_expansion d).and
      (eventually_jointBoundaryScale_bounds d)).and hw)
  refine ⟨max L₀ 2,lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_right _ _),?_⟩
  intro p hp
  let L := Real.log (p:ℕ)/2
  let s := Real.log (1/|jointIntegerLag L|)
  have hL2 : 2 ≤ L := (le_max_right L₀ 2).trans hp
  have hL : 0 < L := by linarith
  obtain ⟨⟨he,hs⟩,hw⟩ := hL₀ L ((le_max_left L₀ 2).trans hp)
  have hslag := jointPrime_log_lag_bounds p (show 1≤L by linarith)
  have hslo : L-Real.log 2 ≤ s := hslag.1
  have hshi : s ≤ 2*L+Real.log 2 := by
    change s ≤ 2*(Real.log (p:ℕ)/2)+Real.log 2
    linarith only [hslag.2]
  obtain ⟨hKlo,hKhi⟩ := hs s hslo hshi
  have hK : 0 < jointBoundaryScale d L s := hL.trans_le hKlo
  refine ⟨hK,?_⟩
  exact ⟨(hw _ hKlo hKhi).2.1,(hw _ hKlo hKhi).2.2.1,he s hslo hshi hK⟩

end RHTower.WeilWorkPBAP
