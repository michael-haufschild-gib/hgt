import GaloisForLFunctions.HTGeometry.LocalAffineSpectralFactorization

/-!
# Finite local interaction families and packet sectors

Every interaction label carries its own finite site support and local matrix. For an arbitrary
packet of active labels, the union of those supports is an exact common tensor sector. The
corresponding analytic eigenvalue branch depends on the spectator configuration only through its
fixed additive onsite energy.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A finite-site matrix generator with one explicitly local matrix for every interaction label. -/
structure FiniteLocalInteractionFamily
    (V E : Type*) [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] where
  support : E → Finset V
  interaction :
    ∀ e, Matrix (LocalConfiguration A (support e))
      (LocalConfiguration A (support e)) ℂ

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Global operator obtained by tensoring a labelled local interaction with the identity. -/
def globalInteraction
    (L : FiniteLocalInteractionFamily V E A) (e : E) :
    Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  liftLocalMatrix (L.support e) (L.interaction e)

/-- Union of the sites touched by an active interaction packet. -/
def packetSiteSupport
    [DecidableEq E] (L : FiniteLocalInteractionFamily V E A)
    (packet : Finset E) : Finset V :=
  packet.biUnion L.support

theorem support_subset_packetSiteSupport
    [DecidableEq E] (L : FiniteLocalInteractionFamily V E A)
    {packet : Finset E} {e : E} (he : e ∈ packet) :
    L.support e ⊆ L.packetSiteSupport packet := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨e, he, hv⟩

/-- One active interaction, lifted only as far as the packet's common site sector. -/
def packetLocalInteraction
    [DecidableEq E] (L : FiniteLocalInteractionFamily V E A)
    (packet : Finset E) :
    {e : E // e ∈ packet} →
      Matrix (LocalConfiguration A (L.packetSiteSupport packet))
        (LocalConfiguration A (L.packetSiteSupport packet)) ℂ :=
  fun e =>
    liftLocalMatrixToSuperset
      (L.support_subset_packetSiteSupport e.2)
      (L.interaction e.1)

/-- Packet-sector lifting reproduces the original global local interaction exactly. -/
theorem lift_packetLocalInteraction_eq_globalInteraction
    [DecidableEq E] (L : FiniteLocalInteractionFamily V E A)
    (packet : Finset E) (e : {e : E // e ∈ packet}) :
    liftLocalMatrix (L.packetSiteSupport packet)
        (L.packetLocalInteraction packet e) =
      L.globalInteraction e.1 := by
  exact liftLocalMatrix_liftLocalMatrixToSuperset
    (L.support_subset_packetSiteSupport e.2) (L.interaction e.1)

/-- **Exact packet-sector spectral locality.** Every active label packet has an analytic global
branch equal to a branch on precisely the union of its sites plus the fixed spectator onsite
energy. -/
theorem exists_packetEigenvalueBranch_add_spectator
    [Fintype E] [DecidableEq E] [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (packet : Finset E) (x : ∀ v, A v) :
    ∃ localBranch globalBranch : ({e : E // e ∈ packet} → ℂ) → ℂ,
      AnalyticAt ℂ localBranch 0 ∧
      AnalyticAt ℂ globalBranch 0 ∧
      localBranch 0 =
        localOnsiteEnergy onsite (L.packetSiteSupport packet)
          (restrictLocalConfiguration (L.packetSiteSupport packet) x) ∧
      globalBranch 0 = onsiteProductEnergy onsite x ∧
      (∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal
              (localOnsiteEnergy onsite (L.packetSiteSupport packet)))
            (L.packetLocalInteraction packet) coupling,
            localBranch coupling) = 0) ∧
      (∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1)
            coupling,
            globalBranch coupling) = 0) ∧
      globalBranch =
        fun coupling =>
          localBranch coupling +
            outsideOnsiteEnergy onsite (L.packetSiteSupport packet)
              (restrictOutsideConfiguration
                (L.packetSiteSupport packet) x) := by
  obtain ⟨localBranch, globalBranch, hla, hga, hl0, hg0,
      hlroot, hgroot, hsplit⟩ :=
    exists_localAffineEigenvalueBranch_add_spectator
      onsite hinj (L.packetSiteSupport packet)
      (L.packetLocalInteraction packet) x
  refine ⟨localBranch, globalBranch, hla, hga, hl0, hg0,
    hlroot, ?_, hsplit⟩
  filter_upwards [hgroot] with coupling hroot
  simpa only [L.lift_packetLocalInteraction_eq_globalInteraction] using hroot

end FiniteLocalInteractionFamily

end GaloisForLFunctions.HTGeometry
