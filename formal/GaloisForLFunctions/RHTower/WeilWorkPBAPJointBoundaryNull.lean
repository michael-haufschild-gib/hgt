import GaloisForLFunctions.RHTower.WeilWorkPBAPJointBoundaryPrime

/-!
# Actual real-null mixtures below the logarithmic one-node boundary

Every nonnegative correction of the literal prime source obeys a positive
physical-mass margin when d > 1. Exact simultaneous corrections make the
sector nonempty at every prescribed correction mass greater than one.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The explicit actual-prime sector has a uniform margin for every real-null correction. -/
theorem exists_jointPrimeBoundary_null_energy {d : ℝ} (hd : 1 < d) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ p : Nat.Primes, L₀ ≤ Real.log (p:ℕ)/2 →
      ∃ hK : 0 < jointBoundaryScale d (Real.log (p:ℕ)/2) (jointPrimeBoundaryLog p),
      let L := Real.log (p:ℕ)/2
      let g := jointPrimeBoundaryTest d p hK
      jointPairFullEnergy g L 0 < 0 ∧
      ∀ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ), (∀ i, 0 ≤ w i) →
        (∀ n:ℕ, 2 ≤ n → (jointClusterMixture g L w t).sum (fun h r => r*logValue h.1 n)=0) →
        ((d-1)*Real.log L/4)*(jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) ≤
          (jointClusterMixture g L w t).sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1)) := by
  let f := jointUnitBumpTest
  let κ := jointSeedBalance f
  have hκ : 0 < κ := jointSeedBalance_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero
  obtain ⟨L₁,hL₁,hcert⟩ := exists_jointPrimeBoundary_cosine_certificate hd
  have hsmall := (tendsto_jointSeedWidth_zero (3*κ)).eventually
    (gt_mem_nhds (Real.log_pos (by norm_num : (1:ℝ)<2)))
  have hw := eventually_jointBoundaryWidth_bounds f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero
  obtain ⟨L₂,hL₂⟩ := eventually_atTop.mp
    (((eventually_jointBoundaryScale_bounds d).and hsmall).and hw)
  refine ⟨max L₁ (max L₂ 3),hL₁.trans_le (le_max_left _ _),?_⟩
  intro p hp
  let L := Real.log (p:ℕ)/2
  let s := jointPrimeBoundaryLog p
  have hL3 : 3 ≤ L := (le_max_right L₂ 3).trans ((le_max_right L₁ _).trans hp)
  have hL : 0 < L := by linarith
  obtain ⟨hK,hm,hc,hn,ha,hcert⟩ := hcert p ((le_max_left _ _).trans hp)
  obtain ⟨⟨hs,hsmall⟩,hw⟩ := hL₂ L
    ((le_max_left L₂ 3).trans ((le_max_right L₁ _).trans hp))
  have hslag := jointPrime_log_lag_bounds p (show 1≤L by linarith)
  have hslo : L-Real.log 2 ≤ s := hslag.1
  have hshi : s ≤ 2*L+Real.log 2 := by
    change Real.log (1/|jointIntegerLag L|) ≤ 2*(Real.log (p:ℕ)/2)+Real.log 2
    linarith only [hslag.2]
  obtain ⟨hKlo,hKhi⟩ := hs s hslo hshi
  let W := jointBoundaryWidth f L (jointBoundaryScale d L s)
  have hW : 0 < W := jointBoundaryWidth_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero L hK
  have hWsmall : W < Real.log 2 := by
    apply lt_of_le_of_lt _ hsmall
    dsimp only [W,jointBoundaryWidth,jointSeedWidth]
    nlinarith only [mul_le_mul_of_nonneg_left hKhi (mul_pos hκ (Real.exp_pos (-L/2))).le]
  have hWL : W < L := by linarith [(hw _ hKlo hKhi).2.2.1]
  let g := jointPrimeBoundaryTest d p hK
  have hg : tsupport g.1.1 ⊆ Icc 0 W := jointDilatedProfile_support jointUnitBumpTest_support hW
  let b := (d-1)*Real.log L
  let c := testMass g.1.1*(2*s-b)
  change ∀ T : ℝ, b*testMass g.1.1/2 ≤ jointPairFullEnergy g L T+
    c*Real.cos (jointIntegerLag L*T) at hcert
  refine ⟨hK,hn,?_⟩
  intro ι hi w t hwpos hz
  letI : Fintype ι := hi
  let q := jointClusterMixture g L w t
  have hindex : 2 ≤ jointNearestInteger L := jointNearestInteger_ge_two (by linarith)
  have hactive : (EF.weilTest g.1.1 g.1.1 (Real.log (jointNearestInteger L)-L)).re ≠ 0 := ha.ne'
  have hphase := joint_phase_of_active_null g hL.le hWsmall hg w t
    (jointNearestInteger L) hindex hactive (hz _ hindex)
  change 1+∑ i,w i*Real.cos (jointIntegerLag L*t i)=0 at hphase
  have hphase' : (∑ i,w i*Real.cos (jointIntegerLag L*t i)) = -1 := by linarith
  have hzero := hcert 0
  simp only [mul_zero,Real.cos_zero,mul_one] at hzero
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hcert (t i)) (hwpos i))
  have heq : (∑ i,w i*(jointPairFullEnergy g L (t i)+c*Real.cos (jointIntegerLag L*t i))) =
      (∑ i,w i*jointPairFullEnergy g L (t i))-c := by
    calc
      _ = (∑ i,w i*jointPairFullEnergy g L (t i))+c*(∑ i,w i*Real.cos (jointIntegerLag L*t i)) := by
        rw [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hphase']; ring
  rw [heq,← Finset.sum_mul] at hsum
  have hbound : (b*testMass g.1.1/2)*(1+∑ i,w i) ≤
      jointPairFullEnergy g L 0+∑ i,w i*jointPairFullEnergy g L (t i) := by
    nlinarith only [hzero,hsum]
  have hmass := jointClusterMixture_testMass g hg hWL hL.le w t
  have henergy := jointClusterMixture_sum_real g L w t (fun h => weilArchRe (EF.weilTest h.1 h.1))
  change q.sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1)) =
    weilArchRe (EF.weilTest (clusterDifference g.1.1 L) (clusterDifference g.1.1 L))+
      ∑ i,w i*jointPairFullEnergy g L (t i) at henergy
  rw [← jointPairFullEnergy_zero g L] at henergy
  change (b/4)*q.sum (fun h r => r*testMass h.1) ≤ q.sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1))
  calc
    _ = (b*testMass g.1.1/2)*(1+∑ i,w i) := by rw [hmass]; ring
    _ ≤ _ := hbound
    _ = _ := henergy.symm

/-- The positive survivor is nonempty for every prescribed correction mass above one. -/
theorem exists_jointPrimeBoundary_sector {d : ℝ} (hd : 1 < d) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ (p : Nat.Primes) (_ : 5 ≤ (p:ℕ)), L₀ ≤ Real.log (p:ℕ)/2 →
      ∃ hK : 0 < jointBoundaryScale d (Real.log (p:ℕ)/2) (jointPrimeBoundaryLog p),
      let L := Real.log (p:ℕ)/2
      let g := jointPrimeBoundaryTest d p hK
      jointPairFullEnergy g L 0 < 0 ∧
      ∀ M : ℝ, 1 < M → ∃ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
        (∀ i, 0 ≤ w i) ∧ (∑ i,w i)=M ∧
        (∀ n:ℕ, 2 ≤ n → (jointClusterMixture g L w t).sum (fun h r => r*logValue h.1 n)=0) ∧
        0 < (jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) ∧
        ((d-1)*Real.log L/4)*(jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) ≤
          (jointClusterMixture g L w t).sum (fun h r => r*weilArchRe (EF.weilTest h.1 h.1)) := by
  let f := jointUnitBumpTest
  let κ := jointSeedBalance f
  have hκ : 0 < κ := jointSeedBalance_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero
  obtain ⟨L₁,hL₁,henergy⟩ := exists_jointPrimeBoundary_null_energy hd
  have hsmall := (tendsto_jointSeedWidth_zero (3*κ)).eventually
    (gt_mem_nhds (Real.log_pos (by norm_num : (1:ℝ)<2)))
  obtain ⟨L₂,hL₂⟩ := eventually_atTop.mp ((eventually_jointBoundaryScale_bounds d).and hsmall)
  refine ⟨max L₁ (max L₂ 3),hL₁.trans_le (le_max_left _ _),?_⟩
  intro p hp hlarge
  let L := Real.log (p:ℕ)/2
  let s := jointPrimeBoundaryLog p
  have hL3 : 3 ≤ L := (le_max_right L₂ 3).trans ((le_max_right L₁ _).trans hlarge)
  have hL : 0 < L := by linarith
  have hlg : Real.log 2 < L := joint_half_log_prime_gt_log_two p hp
  obtain ⟨hK,hn,henergy⟩ := henergy p ((le_max_left _ _).trans hlarge)
  obtain ⟨hs,hsmall⟩ := hL₂ L
    ((le_max_left L₂ 3).trans ((le_max_right L₁ _).trans hlarge))
  have hslag := jointPrime_log_lag_bounds p (show 1≤L by linarith)
  have hslo : L-Real.log 2 ≤ s := hslag.1
  have hshi : s ≤ 2*L+Real.log 2 := by
    change Real.log (1/|jointIntegerLag L|) ≤ 2*(Real.log (p:ℕ)/2)+Real.log 2
    linarith only [hslag.2]
  have hKhi := (hs s hslo hshi).2
  let W := jointBoundaryWidth f L (jointBoundaryScale d L s)
  have hW : 0 < W := jointBoundaryWidth_pos f jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero L hK
  have hWsmall : W < Real.log 2 := by
    apply lt_of_le_of_lt _ hsmall
    dsimp only [W,jointBoundaryWidth,jointSeedWidth]
    nlinarith only [mul_le_mul_of_nonneg_left hKhi (mul_pos hκ (Real.exp_pos (-L/2))).le]
  let g := jointPrimeBoundaryTest d p hK
  have hg : tsupport g.1.1 ⊆ Icc 0 W := jointDilatedProfile_support jointUnitBumpTest_support hW
  refine ⟨hK,hn,?_⟩
  intro M hM
  obtain ⟨ι,hi,w,t,c,hw,_,hwm,hc,_,_,hz,_⟩ :=
    exists_joint_smooth_null_mixture g p hp hWsmall hg 0 M hM
  letI : Fintype ι := hi
  have hnull : ∀ n:ℕ, 2 ≤ n → (jointClusterMixture g L w t).sum (fun h r => r*logValue h.1 n)=0 := by
    simpa only [hc] using hz
  have he := henergy ι hi w t hw hnull
  have hm := jointClusterMixture_testMass g hg (hWsmall.trans hlg) hL.le w t
  change (jointClusterMixture g L w t).sum (fun h r => r*testMass h.1) =
    2*testMass (jointDilatedProfile f.1.1 W)*(1+∑ i,w i) at hm
  rw [jointDilatedProfile_mass f.1.1 hW,hwm] at hm
  refine ⟨ι,hi,w,t,hw,hwm,hnull,?_,he⟩
  rw [hm]
  have hfm := jointUnitBumpTest_mass_pos
  change 0 < 2*(W*testMass jointUnitBumpTest.1.1)*(1+M)
  positivity

end RHTower.WeilWorkPBAP
