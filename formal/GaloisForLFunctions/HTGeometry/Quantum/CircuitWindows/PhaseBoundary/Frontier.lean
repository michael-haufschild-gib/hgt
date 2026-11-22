import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Projection
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.AnalyticFlow

/-! # Closed projected incidences have invariant-null boundaries -/
open Filter Set MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A X : Type*} [CommRing A] [TopologicalSpace X]
variable {ρ : X → A →+* ℝ} {S : Set X}

/-- A frontier point of a closed incidence must kill a coefficient that
is nonzero somewhere on the orbit closure. -/
theorem LocallyCertified.frontier_witness (hc : LocallyCertified ρ S) (hs : IsClosed S)
    {x : X} (hx : x ∈ frontier S) :
    ∃ a : A, ρ x a = 0 ∧ ∃ z, ρ z a ≠ 0 := by
  obtain ⟨a,ha,hw⟩ := hc x (frontier_subset_iff_isClosed.mpr hs hx)
  refine ⟨a,ha,?_⟩
  by_contra! h
  exact hx.2 (mem_interior_iff_mem_nhds.mpr (hw.mono (fun z hz => hz (h z))))

theorem LocallyCertified.frontier_null [Countable A] [MeasurableSpace X]
    (hc : LocallyCertified ρ S) (hs : IsClosed S) (μ : Measure X)
    (hnull : ∀ a : A, (∃ z, ρ z a ≠ 0) → μ {z | ρ z a = 0} = 0) :
    μ (frontier S) = 0 := by
  have hg (a : A) : ∀ᵐ x ∂μ, (∃ z, ρ z a ≠ 0) → ρ x a ≠ 0 := by
    by_cases h : ∃ z, ρ z a ≠ 0
    · exact (measure_eq_zero_iff_ae_notMem.mp (hnull a h)).mono (fun _ hz _ => hz)
    · exact ae_of_all _ (fun _ h' => (h h').elim)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_all_iff.mpr hg] with x hx h
  obtain ⟨a,ha,hn⟩ := hc.frontier_witness hs h
  exact hx a hn ha

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
