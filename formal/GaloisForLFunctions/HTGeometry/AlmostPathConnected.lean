import Mathlib.Topology.Connected.PathConnected

/-!
# Almost path-connected spaces

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Definition 9.5
(`t95n`) and the two facts stated after it: a space is *almost path-connected* when any two of its
points can be approximated by points joined by a continuous path; such a space is preconnected, and
the continuous image of such a space is again almost path-connected.

Preconnectedness follows because a separation `Z = u ⊔ v` would pull back along a path joining a
point of `u` to a point of `v` to a separation of the unit interval.
-/

namespace HTGeometry

open Set

/-- **Deninger, Definition 9.5 (`t95n`).**  A topological space is *almost path-connected* if any
two points can be approximated by points joined by a continuous path. -/
def AlmostPathConnectedSpace (Z : Type*) [TopologicalSpace Z] : Prop :=
  ∀ (z₀ z₁ : Z) (U₀ : Set Z), U₀ ∈ nhds z₀ → ∀ U₁ : Set Z, U₁ ∈ nhds z₁ →
    ∃ w₀ ∈ U₀, ∃ w₁ ∈ U₁, ∃ γ : unitInterval → Z, Continuous γ ∧ γ 0 = w₀ ∧ γ 1 = w₁

variable {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]

/-- An almost path-connected space is preconnected. -/
theorem AlmostPathConnectedSpace.preconnectedSpace (h : AlmostPathConnectedSpace Z) :
    PreconnectedSpace Z := by
  refine ⟨?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnu, hnv⟩ := hcon
  rw [Set.not_subset] at hnu hnv
  obtain ⟨z₁, -, hz₁⟩ := hnu
  obtain ⟨z₀, -, hz₀⟩ := hnv
  have hz₀u : z₀ ∈ u := by
    rcases hcov (mem_univ z₀) with h' | h'
    · exact h'
    · exact absurd h' hz₀
  have hz₁v : z₁ ∈ v := by
    rcases hcov (mem_univ z₁) with h' | h'
    · exact absurd h' hz₁
    · exact h'
  obtain ⟨w₀, hw₀, w₁, hw₁, γ, hγc, hγ0, hγ1⟩ :=
    h z₀ z₁ u (hu.mem_nhds hz₀u) v (hv.mem_nhds hz₁v)
  have hpre : IsPreconnected (univ : Set unitInterval) := isPreconnected_univ
  have hcov' : (univ : Set unitInterval) ⊆ γ ⁻¹' u ∪ γ ⁻¹' v := by
    intro t _
    rcases hcov (mem_univ (γ t)) with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  have hne0 : (univ ∩ γ ⁻¹' u).Nonempty := ⟨0, mem_univ _, by rw [mem_preimage, hγ0]; exact hw₀⟩
  have hne1 : (univ ∩ γ ⁻¹' v).Nonempty := ⟨1, mem_univ _, by rw [mem_preimage, hγ1]; exact hw₁⟩
  obtain ⟨t, -, htu, htv⟩ :=
    hpre (γ ⁻¹' u) (γ ⁻¹' v) (hu.preimage hγc) (hv.preimage hγc) hcov' hne0 hne1
  have hmem : γ t ∈ (univ : Set Z) ∩ (u ∩ v) := ⟨mem_univ (γ t), htu, htv⟩
  rw [hdisj] at hmem
  exact hmem.elim

/-- The continuous image of an almost path-connected space is almost path-connected. -/
theorem AlmostPathConnectedSpace.image (h : AlmostPathConnectedSpace Z) {f : Z → W}
    (hf : Continuous f) (hsurj : Function.Surjective f) : AlmostPathConnectedSpace W := by
  intro y₀ y₁ V₀ hV₀ V₁ hV₁
  obtain ⟨z₀, rfl⟩ := hsurj y₀
  obtain ⟨z₁, rfl⟩ := hsurj y₁
  obtain ⟨w₀, hw₀, w₁, hw₁, γ, hγc, hγ0, hγ1⟩ :=
    h z₀ z₁ (f ⁻¹' V₀) (hf.continuousAt hV₀) (f ⁻¹' V₁) (hf.continuousAt hV₁)
  exact ⟨f w₀, hw₀, f w₁, hw₁, f ∘ γ, hf.comp hγc, by simp [hγ0], by simp [hγ1]⟩

end HTGeometry
