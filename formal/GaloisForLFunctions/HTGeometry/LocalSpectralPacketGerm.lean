import GaloisForLFunctions.HTGeometry.LocalSpectralPacketRestriction

/-!
# Germ compatibility of global and packet-local spectral branches

A globally labelled simple eigenvalue branch, restricted by setting couplings outside a packet to
zero, is the same analytic germ as the branch constructed from that active packet alone. This
closes the consistency step needed to turn exact packet tensor factorization into connected-cluster
statements about one globally labelled spectrum.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

theorem extendCouplingFromPacket_analyticAt
    (packet : Finset E) :
    AnalyticAt ℂ
      (extendCouplingFromPacket packet :
        ({e : E // e ∈ packet} → ℂ) → E → ℂ) 0 := by
  apply AnalyticAt.pi
  intro e
  by_cases he : e ∈ packet
  · have hproj :
        AnalyticAt ℂ
          (fun coupling : {e : E // e ∈ packet} → ℂ =>
            coupling ⟨e, he⟩) 0 :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : {e : E // e ∈ packet} => ℂ) ⟨e, he⟩).analyticAt 0
    simpa [extendCouplingFromPacket, he] using hproj
  · simp [extendCouplingFromPacket, he, analyticAt_const]

/-- **Global/packet germ compatibility.** Every analytic global branch through a simple product
level restricts to the unique packet-sector branch germ when inactive couplings are set to zero. -/
theorem fullBranch_restrictedToPacket_germ_eq_packetBranch
    [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x : ∀ v, A v)
    (branch : (E → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbranch0 : branch 0 = onsiteProductEnergy onsite x)
    (hbranchRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            branch coupling) = 0)
    (packet : Finset E) :
    ∃ localBranch packetBranch : ({e : E // e ∈ packet} → ℂ) → ℂ,
      AnalyticAt ℂ localBranch 0 ∧
      AnalyticAt ℂ packetBranch 0 ∧
      localBranch 0 =
        localOnsiteEnergy onsite (L.packetSiteSupport packet)
          (restrictLocalConfiguration (L.packetSiteSupport packet) x) ∧
      packetBranch 0 = onsiteProductEnergy onsite x ∧
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
            packetBranch coupling) = 0) ∧
      packetBranch =
        (fun coupling =>
          localBranch coupling +
            outsideOnsiteEnergy onsite (L.packetSiteSupport packet)
              (restrictOutsideConfiguration
                (L.packetSiteSupport packet) x)) ∧
      (fun coupling => branch (extendCouplingFromPacket packet coupling))
        =ᶠ[𝓝 0] packetBranch := by
  obtain ⟨localBranch, packetBranch, hlocalAnalytic, hpacketAnalytic,
      hlocal0, hpacket0, hlocalRoot, hpacketRoot, hsplit⟩ :=
    L.exists_packetEigenvalueBranch_add_spectator
      onsite hinj packet x
  have hext := extendCouplingFromPacket_analyticAt (E := E) packet
  have hext0 :
      extendCouplingFromPacket packet
        (0 : {e : E // e ∈ packet} → ℂ) = 0 := by
    funext e
    simp [extendCouplingFromPacket]
  have hpullAnalytic :
      AnalyticAt ℂ
        (fun coupling => branch (extendCouplingFromPacket packet coupling)) 0 :=
    hbranch.fun_comp_of_eq hext hext0
  have hextTendsto :
      Tendsto
        (extendCouplingFromPacket packet :
          ({e : E // e ∈ packet} → ℂ) → E → ℂ)
        (𝓝 0) (𝓝 0) := by
    have hc := hext.continuousAt
    change Tendsto (extendCouplingFromPacket packet) (𝓝 0)
      (𝓝 (extendCouplingFromPacket packet 0)) at hc
    rw [hext0] at hc
    exact hc
  have hpullRoot :
      ∀ᶠ coupling : {e : E // e ∈ packet} → ℂ in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1)
            coupling,
            branch (extendCouplingFromPacket packet coupling)) = 0 := by
    filter_upwards [hextTendsto.eventually hbranchRoot] with coupling hroot
    rw [← L.affineMatrixFamily_extendCouplingFromPacket onsite packet]
    exact hroot
  have hmatrix :
      Tendsto
        (fun coupling : {e : E // e ∈ packet} → ℂ =>
          affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1)
            coupling)
        (𝓝 0)
        (𝓝 (Matrix.diagonal (onsiteProductEnergy onsite))) := by
    have ha :=
      affineMatrixFamily_analyticAt
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1)
        0
    have hzero :
        affineMatrixFamily
          (Matrix.diagonal (onsiteProductEnergy onsite))
          (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1)
          0 =
        Matrix.diagonal (onsiteProductEnergy onsite) := by
      simp [affineMatrixFamily]
    have hc := ha.continuousAt
    change Tendsto
      (affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1))
      (𝓝 0)
      (𝓝 (affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1) 0)) at hc
    rw [hzero] at hc
    exact hc
  have hpullTendsto :
      Tendsto
        (fun coupling => branch (extendCouplingFromPacket packet coupling))
        (𝓝 0) (𝓝 (onsiteProductEnergy onsite x)) := by
    have hc := hpullAnalytic.continuousAt
    have hvalue :
        branch (extendCouplingFromPacket packet
          (0 : {e : E // e ∈ packet} → ℂ)) =
          onsiteProductEnergy onsite x := by
      rw [hext0, hbranch0]
    change Tendsto
      (fun coupling => branch (extendCouplingFromPacket packet coupling))
      (𝓝 0)
      (𝓝 (branch (extendCouplingFromPacket packet 0))) at hc
    rw [hvalue] at hc
    exact hc
  have hpacketTendsto :
      Tendsto packetBranch (𝓝 0)
        (𝓝 (onsiteProductEnergy onsite x)) := by
    have hc := hpacketAnalytic.continuousAt
    change Tendsto packetBranch (𝓝 0) (𝓝 (packetBranch 0)) at hc
    rw [hpacket0] at hc
    exact hc
  have hgerm :=
    simpleDiagonalMatrix_root_germs_unique
      (onsiteProductEnergy onsite) hinj x
      hmatrix hpullTendsto hpacketTendsto hpullRoot hpacketRoot
  exact ⟨localBranch, packetBranch, hlocalAnalytic, hpacketAnalytic,
    hlocal0, hpacket0, hlocalRoot, hpacketRoot, hsplit, hgerm⟩

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
