import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.DenseEmbedding

/-! # Zero sets on the orbit closure of an analytic flow -/
open Filter Set MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {X : Type*} [TopologicalSpace X]

/-- Every dense translated trajectory detects a nonzero continuous function.
Analyticity then leaves at most countably many zero dates on each trajectory. -/
theorem countable_flow_zeros (f : X → ℝ) (hf : Continuous f) (hn : ∃ z, f z ≠ 0)
    (γ : ℝ → X) (hd : DenseRange γ) (ha : AnalyticOnNhd ℝ (f ∘ γ) univ) :
    {t | f (γ t) = 0}.Countable := by
  apply analytic_zero_set_countable ha
  by_contra! h
  have hz : f = fun _ => (0:ℝ) := hd.equalizer hf continuous_const (funext h)
  obtain ⟨z,hn⟩ := hn
  exact hn (congrFun hz z)

/-- Countable zero dates on each orbit imply invariant measure zero.
Fubini first samples an origin, then a time; invariance removes the shift. -/
theorem null_flow_zeros [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [SFinite μ] (τ : ℝ → X → X)
    (hm : Measurable fun p : X × ℝ => τ p.2 p.1)
    (hinv : ∀ t, MeasurePreserving (τ t) μ μ) (hd : ∀ x, DenseRange fun t => τ t x)
    (f : X → ℝ) (hf : Continuous f) (hn : ∃ z, f z ≠ 0)
    (ha : ∀ x, AnalyticOnNhd ℝ (fun t => f (τ t x)) univ) :
    μ {z | f z = 0} = 0 := by
  let Z := {z | f z = 0}
  have hZ : MeasurableSet Z := (isClosed_eq hf continuous_const).measurableSet
  have hrows (x : X) : ∀ᵐ t : ℝ, f (τ t x) ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp ((countable_flow_zeros f hf hn _ (hd x) (ha x)).measure_zero _)
  have hprod : MeasurableSet {p : X × ℝ | f (τ p.2 p.1) ≠ 0} := (hZ.preimage hm).compl
  have hcols := (Measure.ae_ae_comm (μ := μ) (ν := volume) hprod).mp (ae_of_all _ hrows)
  obtain ⟨t,ht⟩ := hcols.exists
  have hpre : μ (τ t ⁻¹' Z) = 0 := measure_eq_zero_iff_ae_notMem.mpr ht
  exact ((hinv t).measure_preimage hZ.nullMeasurableSet).symm.trans hpre

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
