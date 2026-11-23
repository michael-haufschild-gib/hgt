import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.GaussianIntervals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Choosing a regular tolerance before the Gaussian Hamiltonian -/
open Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
open PrescribedTimes ShortWindows
open DiagonalSynthesis (Register)
noncomputable section

/-- Measurability of the orbit-wide critical error in the Gaussian draw. -/
theorem measurable_threshold (k j : ℕ) :
    Measurable (fun ω => criticalHeight (chainGenerator ω k) j) := by
  let n := k+1
  let f (x : PrefixIndex n → ℝ) := criticalHeight (prefixGenerator n x) j
  have hb (x : PrefixIndex n → ℝ) : BddAbove (range (pathGateDistance n j x)) := by
    refine ⟨2,?_⟩
    rintro _ ⟨t,rfl⟩
    let H := prefixGenerator n x
    have hnorm := norm_sub_le (unitaryEvolution H.val t) (1:Register (n+2))
    rw [CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 t),norm_one] at hnorm
    apply (hasProjectiveCircuitApproximation_iff_infDist _ j (2:ℝ)).mp
    refine ⟨1,norm_one,TwoQubitCircuit.one _,Nat.zero_le _,?_⟩
    rw [one_smul,TwoQubitCircuit.one_eval]
    exact hnorm.trans_eq (by norm_num)
  have hf : Measurable f := by
    apply measurable_of_Ioi
    intro a
    have he : f ⁻¹' Ioi a = ⋃ t : ℝ, (fun x => pathGateDistance n j x t) ⁻¹' Ioi a := by
      ext x
      change a < sSup (range (pathGateDistance n j x)) ↔ _
      constructor
      · intro h
        obtain ⟨z,⟨t,rfl⟩,ht⟩ := exists_lt_of_lt_csSup (range_nonempty _) h
        exact mem_iUnion.mpr ⟨t,ht⟩
      · intro h
        obtain ⟨t,ht⟩ := mem_iUnion.mp h
        exact lt_of_lt_of_le ht (le_csSup (hb x) (mem_range_self t))
    rw [he]
    exact (isOpen_iUnion fun t => isOpen_Ioi.preimage (continuous_distance_at_time n j t)).measurableSet
  have hgen (ω : PathPauliDisorder) : prefixGenerator n (prefixPoint k ω) = chainGenerator ω k :=
    Subtype.ext (numberedGenerator_shell (pathPauliDisorderShell ω n))
  have he : (fun ω => criticalHeight (chainGenerator ω k) j) = f ∘ prefixPoint k :=
    funext fun ω => congrArg (fun H => criticalHeight H j) (hgen ω).symm
  rw [he]
  exact hf.comp (gaussian_pauli_prefix_coordinates_law n).measurable

private theorem measurable_exceptional_graph (g : PathPauliDisorder → ℕ → ℕ → ℝ)
    (hg : ∀ k j, Measurable (fun ω => g ω k j)) :
    MeasurableSet {p : PathPauliDisorder × ℝ | p.2 ∈ exceptionalTolerances (g p.1)} := by
  let U (q k j : ℕ) := {p : PathPauliDisorder × ℝ |
    |p.2-g p.1 k j| ≤ 1/(2:ℝ)^(q*k)}
  have hm (q k j) : MeasurableSet (U q k j) :=
    measurableSet_le (measurable_snd.sub ((hg k j).comp measurable_fst)).abs measurable_const
  have he : {p : PathPauliDisorder × ℝ | p.2 ∈ exceptionalTolerances (g p.1)} =
      ⋂ q : ℕ, ⋂ n : ℕ, ⋃ k : ℕ, ⋃ (_ : n ≤ k), ⋃ j : ℕ, ⋃ (_ : j < 2^(8*(k+3))), U q k j := by
    ext p
    simp only [exceptionalTolerances,mem_setOf_eq,frequently_atTop,
      mem_iInter,mem_iUnion,exists_prop,U]
  rw [he]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun n =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hm q k j

/-- For any measurable family of threshold heights, almost every tolerance
chosen before the Gaussian draw avoids its exceptional set. -/
theorem gaussian_regular_for_measurable_heights (g : PathPauliDisorder → ℕ → ℕ → ℝ)
    (hg : ∀ k j, Measurable (fun ω => g ω k j)) :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, e ∉ exceptionalTolerances (g ω) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  apply (Measure.ae_ae_comm (measurable_exceptional_graph g hg).compl).mp
  apply Eventually.of_forall
  intro ω
  have hd : dimH (exceptionalTolerances (g ω)) < ((1:ℝ≥0):ℝ≥0∞) := by
    rw [dimH_exceptionalTolerances]; norm_num
  have hz := hausdorffMeasure_of_dimH_lt hd
  simpa only [ae_iff,not_not,Set.setOf_mem_eq,NNReal.coe_one,MeasureTheory.hausdorffMeasure_real] using hz

/-- Almost every prescribed tolerance is regular for the actual orbit
maximum on almost every frozen Gaussian chain. -/
theorem gaussian_prescribed_regular_tolerances :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, e ∉ chainExceptional ω :=
  gaussian_regular_for_measurable_heights (fun ω k j => criticalHeight (chainGenerator ω k) j)
    measurable_threshold

/-- A typical prescribed error has recurrent exponential intervals within
sub-Hilbert gate deficit of the actual maximum at that same error. -/
theorem gaussian_prescribed_recurrent_intervals :
    ∀ᵐ e : ℝ ∂volume, e ∈ Ioc (0:ℝ) (11/25) → ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ z ∈ Icc a (a+G), ∀ t : ℝ,
            |t| ≤ (2:ℝ)^(γ*(N:ℝ)) → ∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z+t)) →
              m ≤ j+⌊(2:ℝ)^(α*(N:ℝ))⌋₊ := by
  filter_upwards [gaussian_prescribed_regular_tolerances] with e hreg he
  filter_upwards [hreg,gaussian_frozen_maximum_clearance,LocalPatches.gaussian_exponential_precision_compiler]
    with ω hω hmax hsim
  intro γ α hγ hγα hα
  obtain ⟨c,hc⟩ := hmax e he hω
  filter_upwards [hc,hsim c γ α hγ hγα hα.le] with k hk hs
  intro N H
  obtain ⟨m,hP,hm,hcoarse⟩ := hk
  exact ⟨m,hP,hm,recurrent_floor_of_compiler H hcoarse hs⟩

#print axioms gaussian_prescribed_regular_tolerances
#print axioms gaussian_prescribed_recurrent_intervals
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
