import GaloisForLFunctions.HTGeometry.SharedGaugeQuotientFusion

/-!
# Source-coherent intervention synchronization

This module formalizes the algebraic mechanism that supplies the shared gauge used by
quotient--fusion genesis.  One source intervention has one parameter.  Its images in a family of
organs therefore form one synchronized packet, whereas independent local gauge changes form a
larger product packet.

For an additive gauge group, pairwise relative responses are invariant under one global diagonal
intervention, satisfy an exact cocycle law, and reconstruct the entire local packet modulo that
global intervention.  For a linear family of organ responses, the synchronization equalizer is the
intersection of the kernels of all response differences.  If that equalizer is trivial, global
compatibility selects the zero source displacement.

The results are unconditional algebraic identities.  No RH statement, analytic continuation,
positivity assumption, or added axiom is used.
-/

namespace HTGeometry

noncomputable section

/-! ## Diagonal source interventions and complete relative response -/

variable {ι G : Type*} [AddCommGroup G]

/-- Packet produced by one global source intervention acting identically in every organ. -/
def globalInterventionPacket (u : G) : ι → G := fun _ => u

omit [AddCommGroup G] in
@[simp]
theorem globalInterventionPacket_apply (u : G) (i : ι) :
    globalInterventionPacket (ι := ι) u i = u := rfl

/-- Pairwise response of local intervention parameters. -/
def relativeInterventionResponse (t : ι → G) (i j : ι) : G :=
  t j - t i

@[simp]
theorem relativeInterventionResponse_self (t : ι → G) (i : ι) :
    relativeInterventionResponse t i i = 0 := by
  simp [relativeInterventionResponse]

/-- A single global intervention is invisible to every relative response. -/
theorem relativeInterventionResponse_add_global
    (t : ι → G) (u : G) (i j : ι) :
    relativeInterventionResponse (t + globalInterventionPacket u) i j =
      relativeInterventionResponse t i j := by
  simp only [relativeInterventionResponse, Pi.add_apply,
    globalInterventionPacket_apply]
  abel

/-- Relative responses obey the exact Čech/edge cocycle law. -/
theorem relativeInterventionResponse_cocycle
    (t : ι → G) (i j k : ι) :
    relativeInterventionResponse t i j + relativeInterventionResponse t j k =
      relativeInterventionResponse t i k := by
  unfold relativeInterventionResponse
  abel

/-- One anchor and all relative responses reconstruct every local parameter. -/
theorem interventionPacket_anchor_reconstruction
    (t : ι → G) (i₀ i : ι) :
    t i = t i₀ + relativeInterventionResponse t i₀ i := by
  unfold relativeInterventionResponse
  abel

/-- Anchored relative responses are a complete invariant modulo one global intervention. -/
theorem anchoredRelativeResponse_eq_iff_exists_globalIntervention
    (s t : ι → G) (i₀ : ι) :
    (∀ i, relativeInterventionResponse s i₀ i =
        relativeInterventionResponse t i₀ i) ↔
      ∃ u : G, t = s + globalInterventionPacket u := by
  constructor
  · intro h
    refine ⟨t i₀ - s i₀, ?_⟩
    funext i
    have hi := h i
    simp only [relativeInterventionResponse] at hi
    simp only [Pi.add_apply, globalInterventionPacket_apply]
    calc
      t i = (t i - t i₀) + t i₀ := by abel
      _ = (s i - s i₀) + t i₀ := by rw [← hi]
      _ = s i + (t i₀ - s i₀) := by abel
  · rintro ⟨u, rfl⟩ i
    exact (relativeInterventionResponse_add_global s u i₀ i).symm

/-- The complete pairwise packet is a complete invariant modulo one global intervention. -/
theorem pairwiseRelativeResponse_eq_iff_exists_globalIntervention
    (s t : ι → G) (i₀ : ι) :
    (∀ i j, relativeInterventionResponse s i j =
        relativeInterventionResponse t i j) ↔
      ∃ u : G, t = s + globalInterventionPacket u := by
  constructor
  · intro h
    exact (anchoredRelativeResponse_eq_iff_exists_globalIntervention s t i₀).1
      (fun i => h i₀ i)
  · rintro ⟨u, rfl⟩ i j
    exact (relativeInterventionResponse_add_global s u i j).symm

/-- Vanishing relative response means that every local parameter came from one diagonal source
intervention. -/
theorem anchoredRelativeResponse_eq_zero_iff_globalIntervention
    (t : ι → G) (i₀ : ι) :
    (∀ i, relativeInterventionResponse t i₀ i = 0) ↔
      t = globalInterventionPacket (t i₀) := by
  constructor
  · intro h
    funext i
    have hi := h i
    simp only [relativeInterventionResponse] at hi
    simp only [globalInterventionPacket_apply]
    exact sub_eq_zero.mp hi
  · intro h i
    rw [h]
    simp [relativeInterventionResponse]

/-! ## Source formation and equalizer selection -/

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Simultaneous organ packet formed from one source displacement. -/
def sourceInterventionPacket (ρ : ι → V →ₗ[R] W) (x : V) : ι → W :=
  fun i => ρ i x

@[simp]
theorem sourceInterventionPacket_apply
    (ρ : ι → V →ₗ[R] W) (x : V) (i : ι) :
    sourceInterventionPacket ρ x i = ρ i x := rfl

/-- Relative organ response is the corresponding difference representation applied to the one
source displacement. -/
theorem relativeInterventionResponse_sourcePacket
    (ρ : ι → V →ₗ[R] W) (x : V) (i j : ι) :
    relativeInterventionResponse (sourceInterventionPacket ρ x) i j =
      (ρ j - ρ i) x := by
  simp [relativeInterventionResponse, sourceInterventionPacket]

/-- Source displacements whose responses synchronize with a chosen anchor organ. -/
def sourceSynchronizationKernel
    (ρ : ι → V →ₗ[R] W) (i₀ : ι) : Submodule R V :=
  ⨅ i, LinearMap.ker (ρ i - ρ i₀)

/-- Membership in the synchronization kernel is exactly equality of every organ response with the
anchor response. -/
theorem mem_sourceSynchronizationKernel_iff
    (ρ : ι → V →ₗ[R] W) (i₀ : ι) (x : V) :
    x ∈ sourceSynchronizationKernel ρ i₀ ↔ ∀ i, ρ i x = ρ i₀ x := by
  simp [sourceSynchronizationKernel, sub_eq_zero]

/-- If the source response family has trivial synchronization equalizer, one globally compatible
response packet selects only the zero source displacement. -/
theorem sourceSynchronization_selects_zero
    (ρ : ι → V →ₗ[R] W) (i₀ : ι)
    (hsep : sourceSynchronizationKernel ρ i₀ = ⊥)
    {x : V} (hcompat : ∀ i, ρ i x = ρ i₀ x) :
    x = 0 := by
  have hx : x ∈ sourceSynchronizationKernel ρ i₀ :=
    (mem_sourceSynchronizationKernel_iff ρ i₀ x).2 hcompat
  rw [hsep] at hx
  simpa using hx

/-- Closed capstone: one source intervention produces a cocycle-complete relative packet, and a
trivial response equalizer turns global compatibility into exact source selection. -/
theorem sourceCoherentInterventionSynchronization_capstone
    (s t : ι → G) (i₀ : ι)
    (ρ : ι → V →ₗ[R] W) (hsep : sourceSynchronizationKernel ρ i₀ = ⊥)
    {x : V} (hcompat : ∀ i, ρ i x = ρ i₀ x) :
    ((∀ i j, relativeInterventionResponse s i j =
          relativeInterventionResponse t i j) ↔
        ∃ u : G, t = s + globalInterventionPacket u)
      ∧ (∀ i j k,
        relativeInterventionResponse t i j + relativeInterventionResponse t j k =
          relativeInterventionResponse t i k)
      ∧ x = 0 := by
  exact ⟨pairwiseRelativeResponse_eq_iff_exists_globalIntervention s t i₀,
    relativeInterventionResponse_cocycle t,
    sourceSynchronization_selects_zero ρ i₀ hsep hcompat⟩

end

end HTGeometry
