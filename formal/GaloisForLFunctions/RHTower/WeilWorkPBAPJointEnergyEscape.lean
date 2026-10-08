import GaloisForLFunctions.RHTower.WeilWorkPBAPJointEnergy
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointActive

/-!
Actual real-null full-energy escape at correction mass one.
Two real-active nodes imply both unnormalized and mass-normalized energy escape.
This fixed-profile boundary theorem does not prove full PBAP.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Exact physical mass of the constructed finite mixture. -/
theorem jointClusterMixture_testMass {ι : Type} [Fintype ι] (f : JointSmoothTest)
    {L W : ℝ} (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L)
    (hL : 0 ≤ L) (w t : ι → ℝ) :
    (jointClusterMixture f L w t).sum (fun g r => r*testMass g.1) =
      2*testMass f.1.1*(1+∑ i, w i) := by
  have h := congrArg Complex.re (jointClusterMixture_mass f hf hWL hL w t)
  simpa [Finsupp.sum, autocorr_zero_eq_testMass, mul_assoc, mul_left_comm, mul_comm] using h

/-- Actual real-null mixtures escape every full-energy bound near correction mass one. -/
theorem joint_actual_null_energy_escape (f : JointSmoothTest) (p : Nat.Primes)
    (hp : 5 ≤ (p : ℕ)) {W : ℝ} (hW : W < Real.log 2)
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hnp : n < (p : ℕ)) (hmp : m < (p : ℕ))
    (hnm : n ≠ m)
    (han : (EF.weilTest f.1.1 f.1.1 (Real.log n-Real.log (p : ℕ)/2)).re ≠ 0)
    (ham : (EF.weilTest f.1.1 f.1.1 (Real.log m-Real.log (p : ℕ)/2)).re ≠ 0) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) →
      (∀ k : ℕ, 2 ≤ k → (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
        (fun g r => r * logValue g.1 k) = 0) →
      (∑ i, w i) < 1+δ → A <
        (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
          (fun g r => r*weilArchRe (EF.weilTest g.1 g.1)) := by
  let L := Real.log (p : ℕ)/2
  let M := testMass f.1.1
  let C := jointEnergyCost f L
  let E := weilArchRe (EF.weilTest (clusterDifference f.1.1 L) (clusterDifference f.1.1 L))
  have hf0 : f.1.1 ≠ 0 := by
    intro hz
    apply han
    simp [hz, EF.weilTest]
  have hM : 0 < M := joint_testMass_pos f hf0
  have hC : 0 ≤ C := jointEnergyCost_nonneg f L
  have hWL : W < L := hW.trans (joint_half_log_prime_gt_log_two p hp)
  have hL : 0 ≤ L := le_of_lt ((Real.log_pos (by norm_num)).trans
    (joint_half_log_prime_gt_log_two p hp))
  obtain ⟨δ, hδ, hcost⟩ := joint_actual_null_logCost_escape f p hp hW hf
    hn hm hnp hmp hnm han ham ((A-E+2*C)/(2*M))
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro ι hi w t hw hz hmass
  letI : Fintype ι := hi
  have hsmall : (∑ i, w i) < 2 := by linarith [min_le_right δ (1:ℝ)]
  have hcost' := hcost ι hi w t hw hz
    (by linarith [min_le_left δ (1:ℝ)])
  have hc : A-E+2*C < 2*M*(∑ i, w i*Real.log (2+|t i|)) := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2*M)).mp hcost'
    nlinarith only [h]
  have hb := jointClusterMixture_energy_lower f hf hWL hL w t hw
  change E+2*M*(∑ i, w i*Real.log (2+|t i|))-C*(∑ i, w i) ≤ _ at hb
  have hwc := mul_le_mul_of_nonneg_left hsmall.le hC
  linarith

/-- Normalization by actual physical mass preserves full-energy escape. -/
theorem joint_actual_null_normalized_energy_escape (f : JointSmoothTest) (p : Nat.Primes)
    (hp : 5 ≤ (p : ℕ)) {W : ℝ} (hW : W < Real.log 2)
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hnp : n < (p : ℕ)) (hmp : m < (p : ℕ))
    (hnm : n ≠ m)
    (han : (EF.weilTest f.1.1 f.1.1 (Real.log n-Real.log (p : ℕ)/2)).re ≠ 0)
    (ham : (EF.weilTest f.1.1 f.1.1 (Real.log m-Real.log (p : ℕ)/2)).re ≠ 0) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) →
      (∀ k : ℕ, 2 ≤ k → (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
        (fun g r => r * logValue g.1 k) = 0) →
      (∑ i, w i) < 1+δ → A <
        (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
          (fun g r => r*weilArchRe (EF.weilTest g.1 g.1)) /
        (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
          (fun g r => r*testMass g.1) := by
  have hf0 : f.1.1 ≠ 0 := by
    intro hz
    apply han
    simp [hz, EF.weilTest]
  have hM := joint_testMass_pos f hf0
  have hWL : W < Real.log (p : ℕ)/2 := hW.trans (joint_half_log_prime_gt_log_two p hp)
  have hL : 0 ≤ Real.log (p : ℕ)/2 := le_of_lt ((Real.log_pos (by norm_num)).trans
    (joint_half_log_prime_gt_log_two p hp))
  obtain ⟨δ, hδ, henergy⟩ := joint_actual_null_energy_escape f p hp hW hf
    hn hm hnp hmp hnm han ham (6*testMass f.1.1*max A 0)
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro ι hi w t hw hz hmass
  letI : Fintype ι := hi
  have hsmall : (∑ i, w i) < 2 := by linarith [min_le_right δ (1:ℝ)]
  have hnonneg : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  have he := henergy ι hi w t hw hz (by linarith [min_le_left δ (1:ℝ)])
  rw [jointClusterMixture_testMass f hf hWL hL]
  apply (lt_div_iff₀ (by positivity)).2
  have hbound : 2*testMass f.1.1*(1+∑ i, w i) ≤ 6*testMass f.1.1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound (le_max_right A 0)
  have hA := mul_le_mul_of_nonneg_right (le_max_left A 0)
    (by positivity : 0 ≤ 2*testMass f.1.1*(1+∑ i, w i))
  nlinarith only [he, hmul, hA]

end RHTower.WeilWorkPBAP
