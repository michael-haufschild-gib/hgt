import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.SelectedLimit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.SetwiseLimit

/-! # Setwise late observations with a draw-dependent limiting weight -/
open Set Filter MeasureTheory ProbabilityTheory Topology Function
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open private expandingEvents pi_expandingEvents generate_expandingEvents real_union_sum from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.SetwiseLimit
noncomputable section

/-- A ray occupation limit is a measurable, integrable weight on disorder.
It is bounded by one because the interval of dilations from one to two
has length one. -/
theorem integrable_ray_weight {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → (ι → ℝ)) (hX : Measurable X)
    (E : ℝ → Set (ι → ℝ)) (hE : ∀ t, MeasurableSet (E t)) (p : Ω→ℝ)
    (h : ∀ᵐ ω ∂P, Tendsto (fun t => rayMass 2 (E t) (X ω)) atTop (𝓝 (p ω))) :
    Integrable p P := by
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun t : ℝ => ((measurable_rayMass 2 (hE t)).comp hX).aestronglyMeasurable) h
  apply Integrable.of_bound hm 1
  filter_upwards [h] with ω hw
  apply le_of_tendsto hw.norm
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤rayMass 2 (E t) (X ω) from measureReal_nonneg)]
  apply (measureReal_mono (subset_univ _)).trans
  rw [measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le (by norm_num : (1:ℝ)≤2)]
  norm_num

/-- Each measurable selection is weighted by the selected draws' own
limiting phase fractions. Domination by the original Gaussian measure
extends expansion-closed tests to all measurable prefix events. -/
theorem weighted_setwise_limit {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : MeasurePreserving X P (Measure.pi fun _ : ι => gaussianReal 0 1))
    (E : ℝ → Set (ι → ℝ)) (hE : ∀ t, MeasurableSet (E t)) (p : Ω→ℝ)
    (h : ∀ b > (1:ℝ), ∀ᵐ ω ∂P, Tendsto (fun t => rayMass b (E t) (X ω)) atTop (𝓝 ((b-1)*p ω))) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    ∀ B : Set (ι → ℝ), MeasurableSet B →
      Tendsto (fun t => μ.real (B ∩ E t)) atTop (𝓝 (∫ ω in X ⁻¹' B, p ω ∂P)) := by
  intro μ
  have hp := integrable_ray_weight X hX.measurable E hE p (by simpa only [show (2:ℝ)-1=1 by norm_num,one_mul] using h 2 (by norm_num))
  let ν (t : ℝ) := μ.restrict (E t)
  let C (B : Set (ι → ℝ)) := Tendsto (fun t => (ν t).real B) atTop (𝓝 (∫ ω in X ⁻¹' B, p ω ∂P))
  have hbase (B : Set (ι → ℝ)) (hB : B∈expandingEvents ι) : C B := by
    have hh := weighted_selected_snapshot X hX B hB.1 hB.2 E hE p h
    simpa only [C,ν,measureReal_restrict_apply hB.1] using hh
  have hu : C univ := hbase univ ⟨MeasurableSet.univ,fun _ _ _ _ => mem_univ _⟩
  have hall : ∀ B : Set (ι → ℝ), MeasurableSet B → C B := by
    apply MeasurableSpace.induction_on_inter (C:=fun B _ => C B)
      (generate_expandingEvents ι) (pi_expandingEvents ι)
    · simp only [C,measureReal_empty,preimage_empty,setIntegral_empty]; exact tendsto_const_nhds
    · exact hbase
    · intro B hB hlim
      simpa only [C,measureReal_compl hB,preimage_compl,preimage_univ,setIntegral_univ,
        setIntegral_compl (hB.preimage hX.measurable) hp] using hu.sub hlim
    · intro A hd hm hlim
      have hs := summable_measure_toReal (μ:=μ) hm hd
      have hb (t : ℝ) (n : ℕ) : ‖(ν t).real (A n)‖≤μ.real (A n) := by
        rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
        change (μ.restrict (E t)).real (A n)≤_
        rw [measureReal_restrict_apply (hm n)]
        exact measureReal_mono inter_subset_left
      have hh := tendsto_tsum_of_dominated_convergence (f:=fun t n => (ν t).real (A n))
        (g:=fun n => ∫ ω in X ⁻¹' A n, p ω ∂P) hs hlim (Eventually.of_forall hb)
      have hd' : Pairwise (Disjoint on fun n => X ⁻¹' A n) := fun i j hij =>
        Set.disjoint_left.mpr fun _ h₁ h₂ => Set.disjoint_left.mp (hd hij) h₁ h₂
      have hsum := integral_iUnion (fun i => (hm i).preimage hX.measurable) hd' hp.integrableOn
      simpa only [C,real_union_sum _ A hd hm,preimage_iUnion,hsum] using hh
  intro B hB
  simpa only [C,ν,measureReal_restrict_apply hB] using hall B hB

#print axioms weighted_setwise_limit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
