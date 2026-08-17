import Mathlib

/-!
# A locally bounded property on a compact set is uniformly bounded

If a property indexed by a real bound holds, with some bound, on a neighbourhood of every point of a
compact set, and is monotone in the bound, then a single bound works on the whole compact set.

This is the step that turns the pointwise comparison constants of a chartwise argument — each valid
only near one point, with its own constant — into the one constant a Schwarz-type count consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **Uniformisation of a locally bounded property over a compact set.** -/
theorem exists_uniform_bound_of_local {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {p : ℝ → X → Prop}
    (hmono : ∀ (C₁ C₂ : ℝ) (x : X), C₁ ≤ C₂ → p C₁ x → p C₂ x)
    (hloc : ∀ x ∈ K, ∃ U : Set X, U ∈ 𝓝 x ∧ ∃ C : ℝ, ∀ z ∈ U, p C z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, p C z := by
  classical
  choose! U hU C hCspec using hloc
  have hcover : K ⊆ ⋃ x ∈ K, interior (U x) := by
    intro z hz
    exact Set.mem_biUnion hz (mem_interior_iff_mem_nhds.mpr (hU z hz))
  obtain ⟨b, hbsub, hbfin, hbcov⟩ :=
    hK.elim_finite_subcover_image (b := K) (c := fun x => interior (U x))
      (fun x _ => isOpen_interior) hcover
  set s : Finset X := hbfin.toFinset with hs
  have hmemb : ∀ z ∈ K, ∃ x ∈ s, x ∈ K ∧ z ∈ interior (U x) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ : ∃ x ∈ b, z ∈ interior (U x) := by
      have := hbcov hz
      simpa using this
    exact ⟨x, by rwa [hs, Set.Finite.mem_toFinset], hbsub hx, hzx⟩
  rcases Finset.eq_empty_or_nonempty s with hse | hsne
  · refine ⟨0, le_rfl, ?_⟩
    intro z hz
    obtain ⟨x, hx, -, -⟩ := hmemb z hz
    rw [hse] at hx
    exact absurd hx (Finset.notMem_empty x)
  refine ⟨s.sup' hsne (fun x => max 0 (C x)), ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsne
    exact le_trans (le_max_left 0 (C x)) (Finset.le_sup' (fun x => max 0 (C x)) hx)
  · intro z hz
    obtain ⟨x, hx, hxK, hzx⟩ := hmemb z hz
    refine hmono (C x) (s.sup' hsne (fun x => max 0 (C x))) z ?_
      (hCspec x hxK z (interior_subset hzx))
    exact le_trans (le_max_right 0 (C x)) (Finset.le_sup' (fun x => max 0 (C x)) hx)

end GaloisForLFunctions.HTGeometry
