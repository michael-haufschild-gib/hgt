/-
# Endpoint completeness and genericity meet on the chart

Endpoint completeness of the chart eigenvectors holds at all small nonzero coupling on the
anchor-star line, and the anchor-star line stays in the chart near zero; so there is a chart point
at which every ordered pair is endpoint visible.  Endpoint visibility is an *open* condition there,
because the canonical eigenvectors are analytic, and any dense set of parameters therefore contains
a point at which it still holds.

That is the induction step of Lemma A1, stated in the chart's own coordinates: from an old system
with simple split spectrum and an endpoint channel seeing every ordered pair, a generic extended
parameter is again endpoint complete.

Main results:
* `exists_chartPoint_endpointComplete` — a chart point where every ordered pair is visible.
* `exists_mem_dense_chartAdjugate_endpointComplete` — **the intersection with any dense set**.
-/
import GaloisForLFunctions.HTGeometry.AnchorStarAdjugateTransfer
import GaloisForLFunctions.HTGeometry.EndpointCompleteGenericIntersection

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **A chart point at which every ordered pair is endpoint visible.** -/
theorem exists_chartPoint_endpointComplete {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    (C : LocalExtensionEigenbranchChart E (boolShift z) M) :
    ∃ p ∈ C.U, ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (C.adjugateColumn E (boolShift z) M q.1 p)
        (C.adjugateColumn E (boolShift z) M q.2 p) ≠ 0 := by
  have hcoe : Tendsto (fun t : ℝ => ((t : ℝ) : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have h0 : Tendsto (fun t : ℝ => ((t : ℝ) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ))
    exact h0.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ((boolShift z, ((t : ℝ) : ℂ) • anchorStarLayerEdge (false : Bool)) :
        (Bool → ℂ) × Matrix Bool Bool ℂ) ∈ C.U :=
    hcoe.eventually (C.eventually_anchorStar_mem E (boolShift z) M false)
  obtain ⟨t, hcomplete, hU⟩ :=
    ((eventually_forall_chartAdjugate_endpoint_ne_zero hinj hM C).and hmem).exists
  exact ⟨_, hU, hcomplete⟩

/-- **The induction step of Lemma A1 in the chart's coordinates.**  Every dense set of chart
parameters contains one at which the extended system is still endpoint complete. -/
theorem exists_mem_dense_chartAdjugate_endpointComplete {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    (C : LocalExtensionEigenbranchChart E (boolShift z) M)
    {Good : Set ((Bool → ℂ) × Matrix Bool Bool ℂ)} (hdense : Dense Good) :
    ∃ p ∈ Good, ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (C.adjugateColumn E (boolShift z) M q.1 p)
        (C.adjugateColumn E (boolShift z) M q.2 p) ≠ 0 := by
  obtain ⟨p₀, hp₀, hcomplete⟩ := exists_chartPoint_endpointComplete hinj hM C
  refine exists_mem_dense_forall_layerReducedTransition_ne_zero
    (fun i p => C.adjugateColumn E (boolShift z) M i p) ?_ hcomplete hdense
  intro i y
  exact (C.adjugateColumn_analyticAt E (boolShift z) M i p₀ hp₀ y).continuousAt

end

end GaloisForLFunctions.HTGeometry
