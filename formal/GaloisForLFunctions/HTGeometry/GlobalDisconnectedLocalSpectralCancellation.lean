import GaloisForLFunctions.HTGeometry.DisconnectedLocalSpectralPacketCancellation
import GaloisForLFunctions.HTGeometry.LocalSpectralPacketGerm

/-!
# Disconnected cancellation for one global local spectrum

Every packet-sector branch is the restriction of the unique globally labelled
simple spectral germ.  Combining this compatibility with arbitrary-packet
factorization proves disconnected Möbius cancellation directly for one global
local matrix family.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

/-- Restriction from the full coupling space to a finite packet is analytic. -/
theorem restrictCouplingToPacket_analyticAt
    {E : Type*} [Fintype E]
    (packet : Finset E) :
    AnalyticAt ℂ
      (restrictCouplingToPacket packet :
        (E → ℂ) → ({e : E // e ∈ packet} → ℂ)) 0 := by
  apply AnalyticAt.pi
  intro e
  exact (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : E => ℂ) e.1).analyticAt 0

/-- Coupling restriction preserves the zero-coupling germ. -/
theorem restrictCouplingToPacket_tendsto_zero
    {E : Type*} [Fintype E]
    (packet : Finset E) :
    Tendsto
      (restrictCouplingToPacket packet :
        (E → ℂ) → ({e : E // e ∈ packet} → ℂ))
      (𝓝 0) (𝓝 0) := by
  have hc :=
    (restrictCouplingToPacket_analyticAt packet).continuousAt
  simpa [restrictCouplingToPacket] using hc

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- **Global disconnected-cluster law for actual local spectra.**  Let one
analytic eigenvalue branch label a simple product level in the full local
matrix family.  Every interaction packet admitting a nontrivial partition
into label-disjoint parts with disjoint site supports has identically zero
irreducible packet response as a germ at zero coupling. -/
theorem globalBranch_disconnectedPacket_mobius_germ_eq_zero
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : Finset E)
    (hlabel : Disjoint left right)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (hsite :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
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
            branch coupling) = 0) :
    (fun z =>
      finsetMobiusResponse (left ∪ right)
        (fun active =>
          branch (restrictInteractionPacket active z)))
      =ᶠ[𝓝 0] (fun _ : E → ℂ => (0 : ℂ)) := by
  let packet := left ∪ right
  obtain ⟨localBranch, packetBranch, hlocalAnalytic,
      hpacketAnalytic, hlocal0, hpacket0, hlocalRoot,
      hpacketRoot, hsplit, hgerm⟩ :=
    L.fullBranch_restrictedToPacket_germ_eq_packetBranch
      onsite hinj x branch hbranch hbranch0 hbranchRoot packet
  have hpacketZero :=
    L.disconnectedPacketBranch_mobius_germ_eq_zero
      onsite hinj left right hlabel hleft hright hsite x
      packetBranch hpacketAnalytic hpacket0 hpacketRoot
  have hactive :
      ∀ active : Finset {e : E // e ∈ packet},
        (fun z =>
          branch (extendCouplingFromPacket packet
            (restrictInteractionPacket active z)))
          =ᶠ[𝓝 0]
        (fun z =>
          packetBranch (restrictInteractionPacket active z)) := by
    intro active
    have htendsto :
        Tendsto (restrictInteractionPacket active)
          (𝓝 (0 : {e : E // e ∈ packet} → ℂ)) (𝓝 0) := by
      have ha := restrictInteractionPacket_analyticAt active
      have hc := ha.continuousAt
      have hzero :
          restrictInteractionPacket active
            (0 : {e : E // e ∈ packet} → ℂ) = 0 := by
        funext e
        simp [restrictInteractionPacket]
      change Tendsto (restrictInteractionPacket active) (𝓝 0)
        (𝓝 (restrictInteractionPacket active 0)) at hc
      rw [hzero] at hc
      exact hc
    exact hgerm.comp_tendsto htendsto
  have hall :
      ∀ᶠ z : ({e : E // e ∈ packet} → ℂ) in 𝓝 0,
        ∀ active ∈ Finset.Iic
            (Finset.univ : Finset {e : E // e ∈ packet}),
          branch (extendCouplingFromPacket packet
            (restrictInteractionPacket active z)) =
          packetBranch (restrictInteractionPacket active z) := by
    rw [Finset.eventually_all]
    intro active hactiveMem
    exact hactive active
  have hsubtypeZero :
      (fun z : ({e : E // e ∈ packet} → ℂ) =>
        finsetMobiusResponse Finset.univ
          (fun active =>
            branch (extendCouplingFromPacket packet
              (restrictInteractionPacket active z))))
        =ᶠ[𝓝 0]
      (fun _ : ({e : E // e ∈ packet} → ℂ) =>
        (0 : ℂ)) := by
    filter_upwards [hall, hpacketZero] with z hz hz0
    rw [show finsetMobiusResponse Finset.univ
        (fun active =>
          branch (extendCouplingFromPacket packet
            (restrictInteractionPacket active z))) =
      finsetMobiusResponse Finset.univ
        (fun active =>
          packetBranch (restrictInteractionPacket active z)) by
      unfold finsetMobiusResponse
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      exact hz (Finset.univ \ d)
        (Finset.mem_Iic.mpr Finset.sdiff_subset)]
    exact hz0
  have hpull :=
    hsubtypeZero.comp_tendsto
      (restrictCouplingToPacket_tendsto_zero packet)
  filter_upwards [hpull] with z hz
  have hresponse :
      (fun active : Finset {e : E // e ∈ packet} =>
        branch (extendCouplingFromPacket packet
          (restrictInteractionPacket active
            (restrictCouplingToPacket packet z)))) =
      (fun active =>
        branch (restrictInteractionPacket
          (active.map (Function.Embedding.subtype _)) z)) := by
    funext active
    apply congrArg branch
    funext e
    by_cases he : e ∈ packet
    · simp [extendCouplingFromPacket, restrictCouplingToPacket,
        restrictInteractionPacket, he]
    · have hnot :
          e ∉ active.map (Function.Embedding.subtype _) := by
        intro hmem
        obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hmem
        exact he (hae ▸ a.2)
      simp [extendCouplingFromPacket,
        restrictInteractionPacket, he, hnot]
  change finsetMobiusResponse packet
      (fun active =>
        branch (restrictInteractionPacket active z)) = 0
  rw [← finsetMobiusResponse_subtype_univ packet]
  rw [← hresponse]
  simpa [Function.comp_apply] using hz

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
