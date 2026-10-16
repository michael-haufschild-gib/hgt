import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Basic

/-!
# Exact finite observations inside a dense linear core

A dense linear core has the full image of every continuous finite-dimensional
observation. A continuous section with values in the core therefore corrects
approximants without changing their limit. Every observation fibre has a dense
intersection with the original core; no surjectivity onto an oversized target
space is assumed.
-/

open Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A finite observation cannot distinguish the image of a dense core from
the image of the entire ambient space. -/
theorem denseCore_finiteObservation_image (D : Submodule 𝕜 E)
    (hD : Dense (D : Set E)) (P : E →L[𝕜] F) :
    D.map P.toLinearMap = P.toLinearMap.range := by
  apply le_antisymm
  · rintro y ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · rintro y ⟨x, rfl⟩
    have hclosed : IsClosed {z : E | P z ∈ D.map P.toLinearMap} :=
      (D.map P.toLinearMap).closed_of_finiteDimensional.preimage P.continuous
    have hd : (D : Set E) ⊆ {z : E | P z ∈ D.map P.toLinearMap} := by
      intro z hz
      exact ⟨z, hz, rfl⟩
    exact closure_minimal hd hclosed (hD x)

/-- Exact finite constraints preserve approximation in the original norm. -/
theorem exists_denseCore_approximation_same_finiteObservation
    (D : Submodule 𝕜 E) (hD : Dense (D : Set E)) (P : E →L[𝕜] F)
    (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ D, P y = P x ∧ ‖y - x‖ < ε := by
  let R := D.map P.toLinearMap
  have hP : ∀ z : E, P z ∈ R := by
    intro z
    change P z ∈ D.map P.toLinearMap
    rw [denseCore_finiteObservation_image D hD P]
    exact ⟨z, rfl⟩
  let Q : E →L[𝕜] R := P.codRestrict R hP
  let L : D →L[𝕜] R := Q.comp D.subtypeL
  have hL : L.toLinearMap.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    obtain ⟨z, hz, he⟩ := y.property
    refine ⟨⟨z, hz⟩, ?_⟩
    exact Subtype.ext he
  obtain ⟨S, hS⟩ := L.exists_rightInverse_of_surjective hL
  let A : E → E := fun z => z - (S (Q (z-x)) : E)
  have hA : Continuous A :=
    continuous_id.sub (D.subtypeL.continuous.comp
      (S.continuous.comp (Q.continuous.comp (continuous_id.sub continuous_const))))
  have hAx : A x = x := by simp [A]
  have hAQ (z : E) : Q (A z) = Q x := by
    have hs : Q (S (Q (z-x)) : E) = Q (z-x) :=
      congrArg (fun f : R →L[𝕜] R => f (Q (z-x))) hS
    change Q (z - (S (Q (z-x)) : E)) = Q x
    rw [map_sub, hs, map_sub, sub_sub_cancel]
  have hm : A '' (D : Set E) ⊆ {z | z ∈ D ∧ P z = P x} := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨D.sub_mem hw (S (Q (w-x))).property, ?_⟩
    exact congrArg Subtype.val (hAQ w)
  have hx : x ∈ closure {z | z ∈ D ∧ P z = P x} := by
    have hx' := closure_mono hm (mem_closure_image hA.continuousAt (hD x))
    simpa only [hAx] using hx'
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hx ε hε
  refine ⟨y, hy.1, hy.2, ?_⟩
  rwa [dist_comm, dist_eq_norm] at hd

end GaloisForLFunctions.HTGeometry
