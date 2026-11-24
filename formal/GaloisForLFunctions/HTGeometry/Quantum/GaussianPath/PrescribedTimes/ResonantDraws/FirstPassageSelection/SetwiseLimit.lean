import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.DisorderLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.PiSystem

/-! # Conditioning a late scalar observation on any measurable prefix event -/
open Set Filter MeasureTheory ProbabilityTheory Topology Function
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
noncomputable section

private def expandingEvents (ι : Type*) : Set (Set (ι → ℝ)) :=
  {B | MeasurableSet B ∧ expansionClosed B}

private theorem pi_expandingEvents (ι : Type*) : IsPiSystem (expandingEvents ι) := by
  intro S hS T hT _
  exact ⟨hS.1.inter hT.1,fun a ha x hx => ⟨hS.2 a ha x hx.1,hT.2 a ha x hx.2⟩⟩

/-- Positive coordinate upper tails and negative coordinate lower tails
are closed under expansion. Together they generate the product σ-algebra. -/
private theorem generate_expandingEvents (ι : Type*) :
    (inferInstance : MeasurableSpace (ι → ℝ))=MeasurableSpace.generateFrom (expandingEvents ι) := by
  let M := MeasurableSpace.generateFrom (expandingEvents ι)
  apply le_antisymm _ (MeasurableSpace.generateFrom_le fun _ h => h.1)
  change (⨆ i : ι, (borel ℝ).comap (fun x : ι → ℝ => x i))≤M
  apply iSup_le
  intro i
  apply measurable_iff_comap_le.mp
  apply measurable_of_Ioi
  intro r
  by_cases hr : 0≤r
  · apply MeasurableSpace.GenerateMeasurable.basic
    refine ⟨measurableSet_Ioi.preimage (measurable_pi_apply i),?_⟩
    intro a ha x hx
    change r<x i at hx
    change r<a*x i
    exact hx.trans_le (le_mul_of_one_le_left (hr.trans hx.le) ha)
  · have hl : MeasurableSet[M] ((fun x : ι → ℝ => x i) ⁻¹' Iic r) := by
      apply MeasurableSpace.GenerateMeasurable.basic
      refine ⟨measurableSet_Iic.preimage (measurable_pi_apply i),?_⟩
      intro a ha x hx
      change x i≤r at hx
      change a*x i≤r
      have hh := mul_le_mul_of_nonpos_right ha (hx.trans (le_of_not_ge hr))
      simpa only [one_mul] using hh.trans (by simpa only [one_mul] using hx)
    simpa only [←preimage_compl,compl_Iic] using hl.compl

private theorem real_union_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (hd : Pairwise (Disjoint on A)) (hm : ∀ n, MeasurableSet (A n)) :
    μ.real (⋃ n, A n)=∑' n, μ.real (A n) := by
  simp only [measureReal_def,measure_iUnion hd hm,ENNReal.tsum_toReal_eq (fun n => measure_ne_top μ (A n))]

/-- A common quenched occupation limit gives convergence against every
fixed measurable selection of the coefficient vector. Countable disjoint
unions pass to the limit by domination by the original Gaussian law. -/
theorem setwise_snapshot_limit {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : MeasurePreserving X P (Measure.pi fun _ : ι => gaussianReal 0 1))
    (E : ℝ → Set (ι → ℝ)) (hE : ∀ t, MeasurableSet (E t)) (p : ℝ)
    (h : ∀ b > (1:ℝ), ∀ᵐ ω ∂P, Tendsto (fun t => rayMass b (E t) (X ω)) atTop (𝓝 ((b-1)*p))) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    ∀ B : Set (ι → ℝ), MeasurableSet B →
      Tendsto (fun t => μ.real (B ∩ E t)) atTop (𝓝 (μ.real B*p)) := by
  intro μ
  let ν (t : ℝ) := μ.restrict (E t)
  let C (B : Set (ι → ℝ)) := Tendsto (fun t => (ν t).real B) atTop (𝓝 (μ.real B*p))
  have hbase (B : Set (ι → ℝ)) (hB : B∈expandingEvents ι) : C B := by
    have hh := selected_snapshot_limit X hX B hB.1 hB.2 E hE p h
    simpa only [C,ν,measureReal_restrict_apply hB.1] using hh
  have hu : C univ := hbase univ ⟨MeasurableSet.univ,fun _ _ _ _ => mem_univ _⟩
  have hall : ∀ B : Set (ι → ℝ), MeasurableSet B → C B := by
    apply MeasurableSpace.induction_on_inter (C:=fun B _ => C B)
      (generate_expandingEvents ι) (pi_expandingEvents ι)
    · simp only [C,measureReal_empty,zero_mul]; exact tendsto_const_nhds
    · exact hbase
    · intro B hB hlim
      simpa only [C,measureReal_compl hB,sub_mul] using hu.sub hlim
    · intro A hd hm hlim
      have hs := summable_measure_toReal (μ:=μ) hm hd
      have hb (t : ℝ) (n : ℕ) : ‖(ν t).real (A n)‖≤μ.real (A n) := by
        rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
        change (μ.restrict (E t)).real (A n)≤_
        rw [measureReal_restrict_apply (hm n)]
        exact measureReal_mono inter_subset_left
      have hh := tendsto_tsum_of_dominated_convergence (f:=fun t n => (ν t).real (A n))
        (g:=fun n => μ.real (A n)*p) hs hlim (Eventually.of_forall hb)
      simpa only [C,real_union_sum _ A hd hm,tsum_mul_right] using hh
  intro B hB
  simpa only [C,ν,measureReal_restrict_apply hB] using hall B hB

#print axioms setwise_snapshot_limit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
