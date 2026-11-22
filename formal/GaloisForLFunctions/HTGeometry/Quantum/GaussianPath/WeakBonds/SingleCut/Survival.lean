import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.Passage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.LocalMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius

/-! # Ninth-power tails from the first crossing to its actual first return -/
open Filter Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
noncomputable section
open PrescribedTimes

/-- Both the first near-Hilbert crossing and every subsequent half-budget
first wait exceed T on disorder mass at least c/T^9. The constant may
depend on the prefix. The same sector bounds the coefficient norm below. -/
theorem gaussian_one_bond_survival :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∃ c > (0:ℝ), ∀ T ≥ (1:ℝ), c ≤ T^9*μ.real {x | 1 ≤ coefficientNorm x ∧
        T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x} := by
  filter_upwards [gaussian_middle_bond_delays (by norm_num : (0:ℝ)<2)] with k hk
  intro n P μ
  let x₀ := fun i => sepCarrier n 2 0 (pathCoeffEquiv n i)
  obtain ⟨a,r,hr,hw⟩ := hk
  have hzero (i) (hi : i∈bondSites a) : x₀ i=0 := by
    obtain ⟨ab,_,rfl⟩ := Finset.mem_image.mp hi
    change sepCarrier n 2 0 (pathCoeffEquiv n ((pathCoeffEquiv n).symm (Sum.inr (a,ab))))=0
    rw [Equiv.apply_symm_apply]
    change (if ab=(2,2) then (0:ℝ) else 0)=0
    simp
  obtain ⟨c,hc,hboxes⟩ := gaussian_local_box (bondSites a) x₀ hzero (lt_min hr zero_lt_one)
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hmp : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  have hnorm : Continuous (coefficientNorm (n:=n)) := by
    change Continuous (fun x : PrefixIndex n→ℝ => ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖)
    exact continuous_norm.comp (PiLp.continuous_toLp 2 _)
  refine ⟨c,hc,fun T hT => ?_⟩
  obtain ⟨E,hE,hfloor,hnear⟩ := hboxes T hT
  let F := {x | 1 ≤ coefficientNorm x ∧ T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x}
  have hwait : MeasurableSet {x | ∀ s ≤ P/2, T < crossingWait n P s x} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_crossingWait n P s)
  have hm : MeasurableSet F := (measurableSet_le measurable_const hnorm.measurable).inter
    ((measurableSet_lt measurable_const (measurable_crossingOrigin ..)).inter hwait)
  have hsub : X ⁻¹' E ≤ᵐ[pathPauliDisorderLaw] X ⁻¹' F := by
    filter_upwards [hw] with ω hω
    intro he
    obtain ⟨hb,hcut⟩ := hnear _ he
    have hpass := hω T (zero_lt_one.trans_le hT) (fun i => (hb i).trans_le (min_le_left ..)) hcut
    let i : PrefixIndex n := (pathCoeffEquiv n).symm (Sum.inl (0,2))
    have hz : x₀ i=2 := by simp [x₀,i,sepCarrier_onsite]
    have hb₀ := (abs_lt.mp ((hb i).trans_le (min_le_right ..))).1
    rw [hz] at hb₀
    have hcoord : 1 ≤ X ω i := by linarith only [hb₀]
    exact ⟨(hcoord.trans (le_abs_self _)).trans (abs_coord_le_norm (WithLp.toLp 2 (X ω)) i),hpass⟩
  have hmono : μ.real E ≤ μ.real F := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [←hmp.measure_preimage hE.nullMeasurableSet,←hmp.measure_preimage hm.nullMeasurableSet]
    exact measure_mono_ae hsub
  rw [bondSites_card] at hfloor
  exact hfloor.trans (mul_le_mul_of_nonneg_left hmono (pow_nonneg (zero_le_one.trans hT) _))

#print axioms gaussian_one_bond_survival
end
end GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
