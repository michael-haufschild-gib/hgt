import GaloisForLFunctions.RHTower.WeilWorkPBAPJointWidthHigh
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointWidthPhase
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointEnergyEscape

/-!
# A nonempty certified sector with actual negative full seed

A fixed translated nonnegative bump, with source-defined shrinking width, has
negative full seed energy and a constructed active-node cosine certificate at
every height. Every nonnegative finite real-integer-null correction has full
energy at least L/16 times its actual physical mass. At every sufficiently
large prime half-logarithm, corrections exist for every prescribed mass M>1.
The concrete capstones have no source-sign, energy-sign or producer premise.
This restricted sector does not prove full PrimeBlindPositive.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- A fixed, nonnegative real smooth source placed strictly inside the unit interval. -/
def jointUnitBumpTest : JointSmoothTest :=
  ⟨⟨fun u => narrowBumpC 0 (u-1/2),
      ((contDiff_narrowBumpC 0).comp (contDiff_id.sub contDiff_const)).of_le (by norm_cast),
      (hasCompactSupport_narrowBumpC 0).comp_homeomorph (Homeomorph.subRight (1/2:ℝ))⟩,
    (contDiff_narrowBumpC 0).comp (contDiff_id.sub contDiff_const)⟩

private theorem jointUnitBumpTest_one : jointUnitBumpTest.1.1 (1/2)=1 := by
  change narrowBumpC 0 ((1/2:ℝ)-1/2)=1
  rw [sub_self]
  unfold narrowBumpC
  rw [(narrowBump 0).one_of_mem_closedBall (Metric.mem_closedBall_self (narrowBump 0).rIn_pos.le)]
  norm_num

theorem jointUnitBumpTest_support : tsupport jointUnitBumpTest.1.1 ⊆ Icc 0 1 := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have hnu : narrowBumpC 0 (u-1/2) ≠ 0 := hu
  have habs : |u-1/2| ≤ (1/4:ℝ) := by
    by_contra hn
    exact hnu (narrowBumpC_eq_zero 0 (by simpa using lt_of_not_ge hn))
  have h := abs_le.mp habs
  constructor <;> linarith

theorem jointUnitBumpTest_mass_pos : 0 < testMass jointUnitBumpTest.1.1 := by
  have hc : Continuous (fun u => ‖jointUnitBumpTest.1.1 u‖^2) :=
    jointUnitBumpTest.2.continuous.norm.pow 2
  have hs : HasCompactSupport (fun u => ‖jointUnitBumpTest.1.1 u‖^2) :=
    jointUnitBumpTest.1.2.2.comp_left (g:=fun z:ℂ => ‖z‖^2) (by simp)
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs (fun u => sq_nonneg _)
    (x:=1/2) (by rw [jointUnitBumpTest_one]; norm_num)

theorem jointUnitBumpTest_integral_ne_zero : (∫u:ℝ,jointUnitBumpTest.1.1 u) ≠ 0 := by
  have hc : Continuous (fun u:ℝ => narrowBump 0 (u-1/2)) :=
    (narrowBump 0).continuous.comp (continuous_id.sub continuous_const)
  have hs : HasCompactSupport (fun u:ℝ => narrowBump 0 (u-1/2)) :=
    (narrowBump 0).hasCompactSupport.comp_homeomorph (Homeomorph.subRight (1/2:ℝ))
  have hp : 0 < ∫u:ℝ,narrowBump 0 (u-1/2) :=
    hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs (fun _ => (narrowBump 0).nonneg)
      (x:=1/2) (by
        rw [sub_self,(narrowBump 0).one_of_mem_closedBall
          (Metric.mem_closedBall_self (narrowBump 0).rIn_pos.le)]
        norm_num)
  change (∫u:ℝ,((narrowBump 0 (u-1/2):ℝ):ℂ)) ≠ 0
  rw [integral_complex_ofReal]
  exact_mod_cast hp.ne'

theorem jointUnitBumpTest_corr_nonneg (y : ℝ) :
    0 ≤ (EF.weilTest jointUnitBumpTest.1.1 jointUnitBumpTest.1.1 y).re :=
  joint_real_autocorr_nonneg (fun u => narrowBump 0 (u-1/2))
    (fun _ => (narrowBump 0).nonneg) y

/-- The actual balanced source has a constructed cosine certificate at every modulation height. -/
theorem eventually_jointSeed_cosine_certificate (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) (hm : 0 < testMass f.1.1)
    (hB : (∫u:ℝ,f.1.1 u) ≠ 0)
    (hcorr : ∀ y:ℝ, 0 ≤ (EF.weilTest f.1.1 f.1.1 y).re) :
    ∀ᶠ L : ℝ in atTop, ∀ T : ℝ,
      (jointSeedWidth (jointSeedBalance f) L*testMass f.1.1*L)/8 ≤
        jointSeedPairEnergy f (jointSeedBalance f) L T +
          (3/2:ℝ)*(jointSeedWidth (jointSeedBalance f) L*testMass f.1.1*L)*
            Real.cos (jointIntegerLag L*T) := by
  have hκ := jointSeedBalance_pos f hm hB
  have hseed := eventually_jointSeedFullEnergy_balanced_bounds f hf hm hB
  have hhigh := eventually_jointSeedPairEnergy_high f hf hm hκ
  filter_upwards [hseed,hhigh,eventually_jointIntegerLag_low_cos,
    eventually_jointSeedWidth_small (jointSeedBalance f),eventually_ge_atTop (3:ℝ)]
    with L hseed hhigh hlow hWs hL
  intro T
  have hLp : 0 < L := by linarith
  have hW := jointSeedWidth_pos hκ hLp
  have hd : 0 < jointSeedWidth (jointSeedBalance f) L*testMass f.1.1*L :=
    mul_pos (mul_pos hW hm) hLp
  by_cases hT : |T| ≤ Real.exp (7*L/8)
  · have hc := hlow T hT
    have hcd : ∀ y ∈ Icc 0 (jointSeedWidth (jointSeedBalance f) L),
        0 ≤ (EF.weilTest
          (jointDilatedProfile f.1.1 (jointSeedWidth (jointSeedBalance f) L))
          (jointDilatedProfile f.1.1 (jointSeedWidth (jointSeedBalance f) L)) y).re := by
      intro y _
      rw [jointDilatedProfile_corr f.1.1 hW]
      simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      exact mul_nonneg hW.le (hcorr _)
    have he := jointPairFullEnergy_zero_le
      (jointDilatedTest f (jointSeedWidth (jointSeedBalance f) L) hW) (L:=L)
      (jointDilatedProfile_support hf hW) hW (by linarith) hcd T
    rw [jointPairFullEnergy_zero] at he
    change jointSeedFullEnergy f (jointSeedBalance f) L ≤
      jointSeedPairEnergy f (jointSeedBalance f) L T at he
    have hh := mul_nonneg hd.le (sub_nonneg.mpr hc)
    nlinarith [hseed.1]
  · have hh := hhigh T (le_of_not_ge hT)
    have hc := mul_nonneg hd.le (show 0 ≤ Real.cos (jointIntegerLag L*T)+1 by
      linarith [Real.neg_one_le_cos (jointIntegerLag L*T)])
    nlinarith

/-- A fixed explicit source: negative full seed and an actual active-node certificate coexist. -/
theorem eventually_jointUnitBump_negative_seed_certificate :
    ∀ᶠ L : ℝ in atTop,
      jointSeedFullEnergy jointUnitBumpTest (jointSeedBalance jointUnitBumpTest) L < 0 ∧
      2 ≤ jointNearestInteger L ∧
      0 < (EF.weilTest
        (jointDilatedProfile jointUnitBumpTest.1.1 (jointSeedWidth (jointSeedBalance jointUnitBumpTest) L))
        (jointDilatedProfile jointUnitBumpTest.1.1 (jointSeedWidth (jointSeedBalance jointUnitBumpTest) L))
        (jointIntegerLag L)).re ∧
      ∀ T : ℝ,
        (jointSeedWidth (jointSeedBalance jointUnitBumpTest) L*testMass jointUnitBumpTest.1.1*L)/8 ≤
          jointSeedPairEnergy jointUnitBumpTest (jointSeedBalance jointUnitBumpTest) L T +
            (3/2:ℝ)*(jointSeedWidth (jointSeedBalance jointUnitBumpTest) L*testMass jointUnitBumpTest.1.1*L)*
              Real.cos (jointIntegerLag L*T) := by
  have hm := jointUnitBumpTest_mass_pos
  have hB := jointUnitBumpTest_integral_ne_zero
  have hf := jointUnitBumpTest_support
  have hseed := eventually_jointSeedFullEnergy_balanced_bounds jointUnitBumpTest hf hm hB
  have hactive := eventually_jointIntegerLag_active jointUnitBumpTest hm
    (jointSeedBalance_pos jointUnitBumpTest hm hB)
  have hcert := eventually_jointSeed_cosine_certificate jointUnitBumpTest hf hm hB
    jointUnitBumpTest_corr_nonneg
  filter_upwards [hseed,hactive,hcert,eventually_ge_atTop (2:ℝ)] with L hs ha hc hL
  exact ⟨hs.2,jointNearestInteger_ge_two hL,ha,hc⟩

/-- Every real-null finite correction of the explicit negative seed has a physical-mass margin. -/
theorem eventually_jointUnitBump_null_energy :
    ∀ᶠ L : ℝ in atTop, ∀ hL : 0 < L,
      let g := jointDilatedTest jointUnitBumpTest (jointSeedWidth (jointSeedBalance jointUnitBumpTest) L)
        (jointSeedWidth_pos (jointSeedBalance_pos jointUnitBumpTest
          jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero) hL)
      ∀ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ), (∀ i, 0 ≤ w i) →
        (∀ n:ℕ, 2 ≤ n → (jointClusterMixture g L w t).sum (fun h r => r*logValue h.1 n)=0) →
        (L/16)*(jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) ≤
          (jointClusterMixture g L w t).sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1)) := by
  let f := jointUnitBumpTest
  let κ := jointSeedBalance f
  have hκ : 0 < κ := jointSeedBalance_pos f jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero
  have hsmall := (tendsto_jointSeedWidth_zero κ).eventually
    (gt_mem_nhds (Real.log_pos (by norm_num : (1:ℝ)<2)))
  filter_upwards [eventually_jointUnitBump_negative_seed_certificate,hsmall,
    eventually_jointSeedWidth_small κ,eventually_ge_atTop (3:ℝ)] with L hc hsmall hWs hL3
  intro hL
  dsimp only
  intro ι hi w t hw hz
  letI : Fintype ι := hi
  let W := jointSeedWidth κ L
  have hW : 0 < W := jointSeedWidth_pos hκ hL
  let g := jointDilatedTest f W hW
  let c := jointClusterMixture g L w t
  let A := W*testMass f.1.1*L
  change (L/16)*c.sum (fun h r => r*testMass h.1) ≤
    c.sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1))
  have hg : tsupport g.1.1 ⊆ Icc 0 W := jointDilatedProfile_support jointUnitBumpTest_support hW
  have hWL : W < L := hWs.2
  have hactive : (EF.weilTest g.1.1 g.1.1 (Real.log (jointNearestInteger L)-L)).re ≠ 0 :=
    hc.2.2.1.ne'
  have hp := joint_phase_of_active_null g hL.le hsmall hg w t
    (jointNearestInteger L) hc.2.1 hactive (hz _ hc.2.1)
  change 1+∑ i, w i*Real.cos (jointIntegerLag L*t i)=0 at hp
  have hp' : (∑ i, w i*Real.cos (jointIntegerLag L*t i)) = -1 := by linarith
  have hcert : ∀ T:ℝ, A/8 ≤ jointSeedPairEnergy f κ L T +
      (3/2:ℝ)*A*Real.cos (jointIntegerLag L*T) := hc.2.2.2
  have he0 := jointPairFullEnergy_zero g L
  change jointSeedPairEnergy f κ L 0=jointSeedFullEnergy f κ L at he0
  have hc0 := hcert 0
  rw [he0] at hc0
  simp only [mul_zero,Real.cos_zero,mul_one] at hc0
  have hsum : (∑ i, w i*(A/8)) ≤
      ∑ i, w i*(jointSeedPairEnergy f κ L (t i)+(3/2:ℝ)*A*Real.cos (jointIntegerLag L*t i)) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcert (t i)) (hw i))
  have hs : (∑ i, w i*(jointSeedPairEnergy f κ L (t i)+(3/2:ℝ)*A*Real.cos (jointIntegerLag L*t i))) =
      (∑ i, w i*jointSeedPairEnergy f κ L (t i))-(3/2:ℝ)*A := by
    calc
      _ = (∑ i, w i*jointSeedPairEnergy f κ L (t i))+
          (3/2:ℝ)*A*(∑ i, w i*Real.cos (jointIntegerLag L*t i)) := by
        rw [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hp']; ring
  rw [hs,← Finset.sum_mul] at hsum
  have hbound : (A/8)*(1+∑ i,w i) ≤
      jointSeedFullEnergy f κ L+∑ i,w i*jointSeedPairEnergy f κ L (t i) := by nlinarith
  have hm := jointClusterMixture_testMass g hg hWL hL.le w t
  change c.sum (fun h r => r*testMass h.1) =
    2*testMass (jointDilatedProfile f.1.1 W)*(1+∑ i,w i) at hm
  rw [jointDilatedProfile_mass f.1.1 hW] at hm
  have he := jointClusterMixture_sum_real g L w t (fun h => weilArchRe (EF.weilTest h.1 h.1))
  change c.sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1)) =
    jointSeedFullEnergy f κ L+∑ i,w i*jointSeedPairEnergy f κ L (t i) at he
  calc
    _ = (A/8)*(1+∑ i,w i) := by rw [hm]; dsimp only [A]; ring
    _ ≤ _ := hbound
    _ = _ := he.symm

/-- The explicit source specialized to each prime half-logarithm. -/
def jointPrimeUnitTest (p : Nat.Primes) (hp : 5 ≤ (p:ℕ)) : JointSmoothTest :=
  jointDilatedTest jointUnitBumpTest
    (jointSeedWidth (jointSeedBalance jointUnitBumpTest) (Real.log (p:ℕ)/2))
    (jointSeedWidth_pos (jointSeedBalance_pos jointUnitBumpTest
      jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero)
      ((Real.log_pos (by norm_num : (1:ℝ)<2)).trans (joint_half_log_prime_gt_log_two p hp)))

/-- Every sufficiently large prime gives nonempty positive real-null corrections of a negative seed,
for every prescribed correction mass greater than one. The earlier theorem bounds every correction. -/
theorem exists_jointUnitBump_prime_sector :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ (p : Nat.Primes) (hp : 5 ≤ (p:ℕ)),
      L₀ ≤ Real.log (p:ℕ)/2 →
      let L := Real.log (p:ℕ)/2
      let g := jointPrimeUnitTest p hp
      jointSeedFullEnergy jointUnitBumpTest (jointSeedBalance jointUnitBumpTest) L < 0 ∧
      ∀ M : ℝ, 1 < M → ∃ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
        (∀ i, 0 ≤ w i) ∧ (∑ i,w i)=M ∧
        (∀ n:ℕ, 2 ≤ n → (jointClusterMixture g L w t).sum (fun h r => r*logValue h.1 n)=0) ∧
        0 < (jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) ∧
        (L/16)*(jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) ≤
          (jointClusterMixture g L w t).sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1)) := by
  let f := jointUnitBumpTest
  let κ := jointSeedBalance f
  have hκ : 0 < κ := jointSeedBalance_pos f jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero
  have hs := eventually_jointSeedFullEnergy_balanced_bounds f jointUnitBumpTest_support
    jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero
  have hw := (tendsto_jointSeedWidth_zero κ).eventually
    (gt_mem_nhds (Real.log_pos (by norm_num : (1:ℝ)<2)))
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp ((hs.and eventually_jointUnitBump_null_energy).and hw)
  refine ⟨max L₀ 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _),?_⟩
  intro p hp hlarge
  let L := Real.log (p:ℕ)/2
  let g := jointPrimeUnitTest p hp
  have hlg : Real.log 2 < L := joint_half_log_prime_gt_log_two p hp
  have hL : 0 < L := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans hlg
  have hW : 0 < jointSeedWidth κ L := jointSeedWidth_pos hκ hL
  rcases hL₀ L ((le_max_left L₀ 1).trans hlarge) with ⟨⟨hseed,henergy⟩,hwidth⟩
  refine ⟨hseed.2,?_⟩
  intro M hM
  have hg : tsupport g.1.1 ⊆ Icc 0 (jointSeedWidth κ L) :=
    jointDilatedProfile_support jointUnitBumpTest_support hW
  obtain ⟨ι,hi,w,t,c,hw,_,hwm,hc,_,_,hz,_⟩ :=
    exists_joint_smooth_null_mixture g p hp hwidth hg 0 M hM
  letI : Fintype ι := hi
  have hn : ∀ n:ℕ, 2 ≤ n → (jointClusterMixture g L w t).sum (fun h r => r*logValue h.1 n)=0 := by
    simpa only [hc] using hz
  have he := henergy hL ι hi w t hw hn
  have hm := jointClusterMixture_testMass g hg (hwidth.trans hlg) hL.le w t
  change (jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) =
    2*testMass (jointDilatedProfile f.1.1 (jointSeedWidth κ L))*(1+∑ i,w i) at hm
  rw [jointDilatedProfile_mass f.1.1 hW,hwm] at hm
  refine ⟨ι,hi,w,t,hw,hwm,hn,?_,he⟩
  rw [hm]
  have hf := jointUnitBumpTest_mass_pos
  change 0 < 2*(jointSeedWidth κ L*testMass jointUnitBumpTest.1.1)*(1+M)
  positivity

end RHTower.WeilWorkPBAP
