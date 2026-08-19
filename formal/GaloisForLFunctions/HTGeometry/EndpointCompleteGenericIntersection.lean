import GaloisForLFunctions.HTGeometry.LayerExtensionEndpointCompleteness

/-!
# Endpoint completeness meets genericity

The inductive step of endpoint completeness cannot be a propagation: the uncoupled split spectrum
`E_α ± z/2` repeats every old gap once per layer, so distinct ordered gaps never survive the
uncoupled extension.  The coupling is what breaks that degeneracy, and the step is therefore an
*intersection*: endpoint completeness holds on a whole neighbourhood of one point because the
eigenvector family is continuous there, and the maximally projective parameters are dense, so some
parameter enjoys both.

This module records that intersection, in the two forms the induction uses -- against a dense set
and against a residual set.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Endpoint completeness holds on an open neighbourhood of a point where it holds, whenever the
eigenvector family is continuous there. -/
theorem isOpen_nhds_forall_layerReducedTransition_ne_zero
    {P : Type*} [TopologicalSpace P] {p₀ : P}
    (ψ : (A × Bool) → P → (A × Bool → ℂ))
    (hcont : ∀ i y, ContinuousAt (fun p => ψ i p y) p₀)
    (hne : ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (ψ q.1 p₀) (ψ q.2 p₀) ≠ 0) :
    ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧ ∀ p ∈ U,
      ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
        layerReducedTransition (ψ q.1 p) (ψ q.2 p) ≠ 0 := by
  obtain ⟨U, hUsub, hUopen, hp₀⟩ :=
    eventually_nhds_iff.mp (eventually_forall_layerReducedTransition_ne_zero ψ hcont hne)
  exact ⟨U, hUopen, hp₀, hUsub⟩

/-- **The inductive step, as an intersection.**  If the eigenvector family is continuous at one
endpoint-complete parameter and the good parameters are dense, some parameter is both good and
endpoint complete. -/
theorem exists_mem_dense_forall_layerReducedTransition_ne_zero
    {P : Type*} [TopologicalSpace P] {p₀ : P}
    (ψ : (A × Bool) → P → (A × Bool → ℂ))
    (hcont : ∀ i y, ContinuousAt (fun p => ψ i p y) p₀)
    (hne : ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (ψ q.1 p₀) (ψ q.2 p₀) ≠ 0)
    {Good : Set P} (hdense : Dense Good) :
    ∃ p ∈ Good, ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (ψ q.1 p) (ψ q.2 p) ≠ 0 := by
  obtain ⟨U, hUopen, hp₀, hU⟩ :=
    isOpen_nhds_forall_layerReducedTransition_ne_zero ψ hcont hne
  obtain ⟨p, hpGood, hpU⟩ := hdense.exists_mem_open hUopen ⟨p₀, hp₀⟩
  exact ⟨p, hpGood, hU p hpU⟩

/-- The same intersection against a residual set, on a Baire space. -/
theorem exists_mem_residual_forall_layerReducedTransition_ne_zero
    {P : Type*} [TopologicalSpace P] [BaireSpace P] [Nonempty P] {p₀ : P}
    (ψ : (A × Bool) → P → (A × Bool → ℂ))
    (hcont : ∀ i y, ContinuousAt (fun p => ψ i p y) p₀)
    (hne : ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (ψ q.1 p₀) (ψ q.2 p₀) ≠ 0)
    {Good : Set P} (hres : Good ∈ residual P) :
    ∃ p ∈ Good, ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (ψ q.1 p) (ψ q.2 p) ≠ 0 :=
  exists_mem_dense_forall_layerReducedTransition_ne_zero ψ hcont hne (dense_of_mem_residual hres)

end

end GaloisForLFunctions.HTGeometry
