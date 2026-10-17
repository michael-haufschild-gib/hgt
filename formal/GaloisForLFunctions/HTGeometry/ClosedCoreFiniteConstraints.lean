import GaloisForLFunctions.HTGeometry.DenseCoreFiniteConstraints

/-! # Exact finite observations inside the closure of a linear image -/

open Set Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem exists_closedCore_approximation_same_finiteObservation
    (D : Submodule 𝕜 E) (P : E →L[𝕜] F) {x : E}
    (hx : x ∈ D.topologicalClosure) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ D, P y = P x ∧ ‖y-x‖ < ε := by
  let C := D.topologicalClosure
  let D' : Submodule 𝕜 C := D.comap C.subtype
  have hd : Dense (D' : Set C) := by
    intro z
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.mp z.property δ hδ
    exact ⟨⟨w, D.le_topologicalClosure hw⟩, hw, hd⟩
  obtain ⟨y, hy, he, hn⟩ := exists_denseCore_approximation_same_finiteObservation
    D' hd (P.comp C.subtypeL) ⟨x, hx⟩ hε
  exact ⟨y, hy, he, hn⟩

theorem mem_closure_closedCore_finiteObservation_fibre
    (D : Submodule 𝕜 E) (P : E →L[𝕜] F) {x : E}
    (hx : x ∈ D.topologicalClosure) :
    x ∈ closure {y : E | y ∈ D ∧ P y = P x} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨y, hy, he, hn⟩ := exists_closedCore_approximation_same_finiteObservation D P hx hε
  refine ⟨y, ⟨hy, he⟩, ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using hn

end GaloisForLFunctions.HTGeometry
