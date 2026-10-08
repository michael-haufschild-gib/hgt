import GaloisForLFunctions.RHTower.WeilWorkPBAPJointBoundaryObstruction
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointBoundaryCertificate

/-!
# Actual-prime transfer of the logarithmic one-node classification

The phase scale and active node are derived from the literal prime half-log,
not supplied by a phase-cost or positivity premise.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The inverse logarithmic lag of the actual nearest integer. -/
def jointPrimeBoundaryLog (p : Nat.Primes) : ℝ :=
  Real.log (1/|jointIntegerLag (Real.log (p:ℕ)/2)|)

theorem jointPrimeBoundaryLog_phase (p : Nat.Primes) :
    Real.exp (-jointPrimeBoundaryLog p)=|jointIntegerLag (Real.log (p:ℕ)/2)| := by
  have hlag : 0 < |jointIntegerLag (Real.log (p:ℕ)/2)| :=
    abs_pos.mpr (jointPrime_integer_lag_neg p).ne
  rw [jointPrimeBoundaryLog,Real.exp_neg,Real.exp_log (div_pos (by norm_num) hlag)]
  simp only [one_div,inv_inv]

theorem jointPrimeBoundaryLog_cos (p : Nat.Primes) (T : ℝ) :
    Real.cos (Real.exp (-jointPrimeBoundaryLog p)*T)=
      Real.cos (jointIntegerLag (Real.log (p:ℕ)/2)*T) := by
  rw [jointPrimeBoundaryLog_phase,abs_of_neg (jointPrime_integer_lag_neg p),neg_mul,Real.cos_neg]

/-- Nearest-node activity holds uniformly for every width above the balanced lower width. -/
theorem eventually_jointIntegerLag_active_uniform (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, ∀ (W : ℝ) (_ : 0 < W), jointSeedWidth κ L ≤ W →
      0 < (EF.weilTest (jointDilatedProfile f.1.1 W)
        (jointDilatedProfile f.1.1 W) (jointIntegerLag L)).re := by
  have hc : Continuous (fun y => (EF.weilTest f.1.1 f.1.1 y).re) :=
    Complex.continuous_re.comp
      (EF.weilTest_contDiff f.1.2.1 f.2.continuous f.1.2.2).continuous
  have hz : 0 < (EF.weilTest f.1.1 f.1.1 0).re := by
    simpa only [autocorr_zero_eq_testMass,Complex.ofReal_re] using hm
  have he := (hc.tendsto 0).eventually (lt_mem_nhds hz)
  obtain ⟨ε,hε,hnear⟩ := Metric.eventually_nhds_iff.mp he
  have ht := (tendsto_jointIntegerLag_div_width hκ).abs
  simp only [abs_zero] at ht
  have hsmall := ht.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall,eventually_gt_atTop (0:ℝ)] with L hs hL
  intro W hW hWlo
  have hW0 := jointSeedWidth_pos hκ hL
  rw [abs_div,abs_of_pos hW0] at hs
  have hr : |W⁻¹*jointIntegerLag L| < ε := by
    calc
      _ = |jointIntegerLag L|/W := by rw [abs_mul,abs_inv,abs_of_pos hW]; ring
      _ ≤ |jointIntegerLag L|/jointSeedWidth κ L :=
        div_le_div_of_nonneg_left (abs_nonneg _) hW0 hWlo
      _ < _ := hs
  have hp := hnear (by simpa only [Real.dist_eq,sub_zero] using hr)
  rw [jointDilatedProfile_corr f.1.1 hW]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_pos hW hp

/-- Every scale in the boundary interval still has a strictly negative literal seed. -/
theorem eventually_jointUnitBump_boundary_negative_seed (d : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ s : ℝ, L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      ∀ hK : 0 < jointBoundaryScale d L s,
      let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
      let hW := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
        jointUnitBumpTest_integral_ne_zero L hK
      jointPairFullEnergy (jointDilatedTest jointUnitBumpTest W hW) L 0 < 0 := by
  let f := jointUnitBumpTest
  let κ := jointSeedBalance f
  let C := jointSeedLogCost f/testMass f.1.1+2
  have hκ : 0 < κ := jointSeedBalance_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero
  have hseed := eventually_joint_boundary_seed_error f jointUnitBumpTest_support
    jointUnitBumpTest_corr_nonneg jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero
  filter_upwards [hseed,eventually_jointBoundaryScale_bounds d,
    eventually_ge_atTop (1/κ),eventually_gt_atTop C,eventually_gt_atTop (0:ℝ)]
    with L hseed hscale hLκ hLC hL
  intro s hslo hshi hK
  let K := jointBoundaryScale d L s
  let W := jointBoundaryWidth f L K
  have hW : 0 < W := jointBoundaryWidth_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero L hK
  have hm : 0 < W*testMass f.1.1 := mul_pos hW jointUnitBumpTest_mass_pos
  obtain ⟨hKlo,hKhi⟩ := hscale s hslo hshi
  have hκK : 1 ≤ κ*K := by
    have h1 := (div_le_iff₀ hκ).mp hLκ
    have h2 := mul_le_mul_of_nonneg_left hKlo hκ.le
    change κ*L ≤ κ*K at h2
    nlinarith only [h1,h2]
  have hlog := Real.log_nonneg hκK
  have h := (abs_le.mp (hseed K hK hKlo hKhi)).2
  simp only at h ⊢
  change jointPairFullEnergy (jointDilatedTest f W hW) L 0/(W*testMass f.1.1)+
    2*Real.log W+2*K ≤ C at h
  have hwlog : Real.log W=Real.log (κ*K)-L/2 := by
    rw [show W=κ*K*Real.exp (-L/2) from rfl,
      Real.log_mul (mul_pos hκ hK).ne' (Real.exp_pos _).ne',Real.log_exp]
    ring
  rw [hwlog] at h
  have hn : jointPairFullEnergy (jointDilatedTest f W hW) L 0/(W*testMass f.1.1)<0 := by
    change L ≤ K at hKlo
    linarith only [h,hlog,hKlo,hLC]
  simpa only [zero_mul] using (div_lt_iff₀ hm).mp hn

/-- The literal dilated unit bump at the actual prime boundary width. -/
def jointPrimeBoundaryTest (d : ℝ) (p : Nat.Primes)
    (hK : 0 < jointBoundaryScale d (Real.log (p:ℕ)/2) (jointPrimeBoundaryLog p)) :
    JointSmoothTest :=
  jointDilatedTest jointUnitBumpTest
    (jointBoundaryWidth jointUnitBumpTest (Real.log (p:ℕ)/2)
      (jointBoundaryScale d (Real.log (p:ℕ)/2) (jointPrimeBoundaryLog p)))
    (jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
      jointUnitBumpTest_integral_ne_zero _ hK)

/-- At actual primes, every one-node coefficient fails on the d<1 side. -/
theorem exists_jointPrimeBoundary_no_cosine {d : ℝ} (hd : d < 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ p : Nat.Primes, L₀ ≤ Real.log (p:ℕ)/2 →
      ∃ hK : 0 < jointBoundaryScale d (Real.log (p:ℕ)/2) (jointPrimeBoundaryLog p),
      ¬ ∃ c : ℝ, ∀ T : ℝ,
        -c*Real.cos (jointIntegerLag (Real.log (p:ℕ)/2)*T) ≤
          jointPairFullEnergy (jointPrimeBoundaryTest d p hK) (Real.log (p:ℕ)/2) T := by
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    ((eventually_jointUnitBump_boundary_no_cosine hd).and (eventually_jointBoundaryScale_bounds d))
  refine ⟨max L₀ 2,lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_right _ _),?_⟩
  intro p hp
  let L := Real.log (p:ℕ)/2
  let s := jointPrimeBoundaryLog p
  have hL2 : 2 ≤ L := (le_max_right L₀ 2).trans hp
  have hL : 0 < L := by linarith
  obtain ⟨hn,hscale⟩ := hL₀ L ((le_max_left L₀ 2).trans hp)
  have hslag := jointPrime_log_lag_bounds p (show 1≤L by linarith)
  have hslo : L-Real.log 2 ≤ s := hslag.1
  have hshi : s ≤ 2*L+Real.log 2 := by
    change Real.log (1/|jointIntegerLag L|) ≤ 2*(Real.log (p:ℕ)/2)+Real.log 2
    linarith only [hslag.2]
  have hK := hL.trans_le (hscale s hslo hshi).1
  refine ⟨hK,?_⟩
  rintro ⟨c,hc⟩
  apply hn s hslo hshi hK
  refine ⟨c,fun T => ?_⟩
  rw [jointPrimeBoundaryLog_cos]
  exact hc T

/-- Actual-prime negative seeds have an explicit positive global certificate on the d>1 side. -/
theorem exists_jointPrimeBoundary_cosine_certificate {d : ℝ} (hd : 1 < d) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ p : Nat.Primes, L₀ ≤ Real.log (p:ℕ)/2 →
      ∃ hK : 0 < jointBoundaryScale d (Real.log (p:ℕ)/2) (jointPrimeBoundaryLog p),
      let L := Real.log (p:ℕ)/2
      let s := jointPrimeBoundaryLog p
      let g := jointPrimeBoundaryTest d p hK
      let m := testMass g.1.1
      let c := m*(2*s-(d-1)*Real.log L)
      0 < m ∧ 0 < c ∧ jointPairFullEnergy g L 0 < 0 ∧
      0 < (EF.weilTest g.1.1 g.1.1 (jointIntegerLag L)).re ∧
      ∀ T : ℝ, (d-1)*Real.log L*m/2 ≤
        jointPairFullEnergy g L T+c*Real.cos (jointIntegerLag L*T) := by
  let f := jointUnitBumpTest
  let κ := jointSeedBalance f
  have hκ : 0 < κ := jointSeedBalance_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero
  have hw := eventually_jointBoundaryWidth_bounds f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    ((((eventually_jointUnitBump_boundary_cosine_certificate hd).and
      (eventually_jointBoundaryScale_bounds d)).and hw).and
      ((eventually_jointIntegerLag_active_uniform f jointUnitBumpTest_mass_pos hκ).and
        (eventually_jointUnitBump_boundary_negative_seed d)))
  refine ⟨max L₀ 2,lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_right _ _),?_⟩
  intro p hp
  let L := Real.log (p:ℕ)/2
  let s := jointPrimeBoundaryLog p
  have hL2 : 2 ≤ L := (le_max_right L₀ 2).trans hp
  have hL : 0 < L := by linarith
  obtain ⟨⟨⟨hc,hscale⟩,hw⟩,⟨ha,hn⟩⟩ := hL₀ L ((le_max_left L₀ 2).trans hp)
  have hslag := jointPrime_log_lag_bounds p (show 1≤L by linarith)
  have hslo : L-Real.log 2 ≤ s := hslag.1
  have hshi : s ≤ 2*L+Real.log 2 := by
    change Real.log (1/|jointIntegerLag L|) ≤ 2*(Real.log (p:ℕ)/2)+Real.log 2
    linarith only [hslag.2]
  obtain ⟨hKlo,hKhi⟩ := hscale s hslo hshi
  have hK := hL.trans_le hKlo
  refine ⟨hK,?_⟩
  let W := jointBoundaryWidth f L (jointBoundaryScale d L s)
  have hW : 0 < W := jointBoundaryWidth_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero L hK
  let g := jointPrimeBoundaryTest d p hK
  have hm : testMass g.1.1=W*testMass f.1.1 := jointDilatedProfile_mass f.1.1 hW
  have hmp : 0 < testMass g.1.1 := by
    rw [hm]
    exact mul_pos hW jointUnitBumpTest_mass_pos
  have hcert := hc s hslo hshi hK
  have hactive := ha W hW (hw _ hKlo hKhi).2.2.2
  refine ⟨hmp,mul_pos hmp hcert.1,hn s hslo hshi hK,hactive,?_⟩
  intro T
  have h := hcert.2 T
  change (d-1)*Real.log L/2 ≤ jointPairFullEnergy g L T/(W*testMass f.1.1)+
    (2*s-(d-1)*Real.log L)*Real.cos (Real.exp (-s)*T) at h
  rw [← hm,jointPrimeBoundaryLog_cos] at h
  have hmul := mul_le_mul_of_nonneg_right h hmp.le
  rw [add_mul,div_mul_cancel₀ _ hmp.ne'] at hmul
  change (d-1)*Real.log L*testMass g.1.1/2 ≤
    jointPairFullEnergy g L T+(testMass g.1.1*(2*s-(d-1)*Real.log L))*
      Real.cos (jointIntegerLag L*T)
  nlinarith only [hmul]

end RHTower.WeilWorkPBAP
