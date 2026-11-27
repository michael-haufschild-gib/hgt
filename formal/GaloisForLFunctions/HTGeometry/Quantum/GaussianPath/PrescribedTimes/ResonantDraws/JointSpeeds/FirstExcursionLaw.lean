import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.Occupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.BudgetLaw

/-! # Joint snapshots after the original first crossing and first return -/
open Set MeasureTheory ProbabilityTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws FirstPassageSelection
open private equal_interval_mass from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.PhysicalRays
noncomputable section
variable {I : Type} [Fintype I]

private theorem measurable_pattern {α : Type*} [MeasurableSpace α] (A : I→Set α)
    (hm : ∀ i, MeasurableSet (A i)) (hit : I→Bool) :
    MeasurableSet {x | ∀ i, (x∈A i ↔ hit i=true)} := by
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  cases hit i
  · exact ((hm i).compl).congr (Set.ext fun x => by simp only [mem_compl_iff,mem_setOf_eq,Bool.false_eq_true,iff_false])
  · exact (hm i).congr (Set.ext fun x => by simp only [mem_setOf_eq,iff_true])

private theorem measurable_clock_test (n s : ℕ) (x : PrefixIndex n→ℝ) (o c ε : ℝ) :
    MeasurableSet {t : ℝ | pathGateDistance n s x (o+c*t)≤ε} := by
  have ht : Continuous (fun t : ℝ => o+c*t) := continuous_const.add (continuous_const.mul continuous_id)
  have hg : Continuous (fun t : ℝ => (x,o+c*t)) := continuous_const.prodMk ht
  exact measurableSet_Iic.preimage ((continuous_distance n s).comp hg).measurable

/-- Over any measurable selection of original prefixes, the joint
snapshot law is the selected mixture of each draw's independent phase
tests. The starts can themselves depend on the selected prefix. -/
private theorem selected_probes (k : ℕ) (c : I→ℝ) (hc : RationallyIndependentFrequency c)
    (hit : I→Bool) (s : I→ℕ) (ε : I→ℝ) (o : I→(PrefixIndex (k+1)→ℝ)→ℝ)
    (ho : ∀ i, Measurable (o i)) (hcov : ∀ a > (0:ℝ), ∀ x i, a*o i (a • x)=o i x) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
    ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B →
      Tendsto (fun t => μ.real (B ∩ {x | ∀ i, (pathGateDistance n (s i) x (o i x+c i*t)≤ε i) ↔ hit i=true}))
        atTop (𝓝 (∫ ω in X ⁻¹' B, ∏ i, let p := affordablePhaseMass k (s i) (ε i) ω
          if hit i then p else 1-p ∂pathPauliDisorderLaw)) := by
  intro n μ X
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let S (t : ℝ) := {x | ∀ i, (pathGateDistance n (s i) x (o i x+c i*t)≤ε i) ↔ hit i=true}
  have hm t : MeasurableSet (S t) := measurable_pattern
    (fun i => {x | pathGateDistance n (s i) x (o i x+c i*t)≤ε i})
    (fun i => measurable_origin_event n (s i) (ε i) (c i*t) (o i) (ho i)) hit
  refine weighted_setwise_limit X (gaussian_pauli_prefix_coordinates_law n) S hm
    (fun ω => ∏ i, if hit i then affordablePhaseMass k (s i) (ε i) ω
      else 1-affordablePhaseMass k (s i) (ε i) ω) ?_
  intro b hb
  filter_upwards [gaussian_joint_affordable_fraction c hc] with ω hw
  let x := X ω
  let A := {v : ℝ | ∀ i, (pathGateDistance n (s i) x (o i x+c i*v)≤ε i) ↔ hit i=true}
  have hA : MeasurableSet A := measurable_pattern
    (fun i => {v : ℝ | pathGateDistance n (s i) x (o i x+c i*v)≤ε i})
    (fun i => measurable_clock_test n (s i) x (o i x) (c i) (ε i)) hit
  have h := hw k hit s ε (fun i => o i x) (fun _ => 0)
  simp only [zero_add] at h
  apply (dilation_interval_limit hA _ h hb).congr
  intro t
  apply equal_interval_mass
  intro a ha
  apply forall_congr'
  intro i
  change (pathGateDistance n (s i) x (o i x+c i*(a*t))≤ε i ↔ hit i=true) ↔
    (pathGateDistance n (s i) (a • x) (o i (a • x)+c i*t)≤ε i ↔ hit i=true)
  rw [distance_dilate,mul_add,hcov a (zero_lt_one.trans_le ha.1) x i,mul_left_comm a (c i) t]

/-- Each observation can start at the actual crossing or the actual
first return to its own low budget. Every pattern of successes and
failures has the same product-mixture limit. -/
theorem joint_first_excursion_snapshot (k P : ℕ) (c : I→ℝ) (hc : RationallyIndependentFrequency c)
    (afterReturn hit : I→Bool) (r s : I→ℕ) (ε : I→ℝ) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
    let σ := crossingOrigin n P (9/80)
    let o := fun i x => if afterReturn i then σ x+crossingWait n P (r i) x else σ x
    ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B →
      Tendsto (fun t => μ.real (B ∩ {x | ∀ i, (pathGateDistance n (s i) x (o i x+c i*t)≤ε i) ↔ hit i=true}))
        atTop (𝓝 (∫ ω in X ⁻¹' B, ∏ i, let p := affordablePhaseMass k (s i) (ε i) ω
          if hit i then p else 1-p ∂pathPauliDisorderLaw)) := by
  intro n μ X σ o
  apply selected_probes k c hc hit s ε o
  · intro i
    cases h : afterReturn i <;> simp only [o,h,Bool.false_eq_true,if_false,if_true]
    · exact measurable_crossingOrigin ..
    · exact (measurable_crossingOrigin ..).add (measurable_crossingWait ..)
  · intro a ha x i
    cases h : afterReturn i <;> simp only [o,h,Bool.false_eq_true,if_false,if_true,σ,
      mul_add,smul_crossingOrigin _ _ _ ha,smul_crossingWait _ _ _ ha]

#print axioms joint_first_excursion_snapshot
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
