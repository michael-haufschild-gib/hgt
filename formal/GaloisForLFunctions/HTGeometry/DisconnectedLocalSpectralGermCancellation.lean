import GaloisForLFunctions.HTGeometry.DisconnectedLocalSpectralCancellation
import GaloisForLFunctions.HTGeometry.FinsetPosetMobiusBridge

/-!
# Branch-independent disconnected spectral cancellation

Disconnected local interaction sectors factor as a Kronecker sum.  The simple
diagonal root selects a unique analytic spectral germ, so the exact vanishing
of the full cross-sector Möbius response holds for every analytic branch
through that root, not only for a chosen factorized branch.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

/-- Restricting a finite coupling family to one interaction packet is analytic. -/
theorem restrictInteractionPacket_analyticAt
    {E : Type*} [Fintype E] [DecidableEq E]
    (packet : Finset E) :
    AnalyticAt ℂ
      (fun coupling : E → ℂ =>
        restrictInteractionPacket packet coupling) 0 := by
  apply AnalyticAt.pi
  intro e
  by_cases he : e ∈ packet
  · have hproj :
        AnalyticAt ℂ (fun coupling : E → ℂ => coupling e) 0 :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : E => ℂ) e).analyticAt 0
    simpa [restrictInteractionPacket, he] using hproj
  · simp [restrictInteractionPacket, he, analyticAt_const]

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- **Branch-independent disconnected cancellation.**  Let two nonempty
interaction packets have disjoint site supports.  Every analytic eigenvalue
branch through a simple product level has vanishing full cross-packet Möbius
response as a germ at zero coupling. -/
theorem disconnectedLocalBranch_crossPacket_germ_eq_zero
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : Finset E)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    (x : ∀ v, A v)
    (branch :
      (Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbranch0 : branch 0 = onsiteProductEnergy onsite x)
    (hbranchRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (L.splitPacketGlobalInteraction left right)
            coupling,
            branch coupling) = 0) :
    let fullPacket :=
      (Finset.univ : Finset {e : E // e ∈ left}).map
          (sumInlEmbedding {e : E // e ∈ left} {e : E // e ∈ right}) ∪
        (Finset.univ : Finset {e : E // e ∈ right}).map
          (sumInrEmbedding {e : E // e ∈ left} {e : E // e ∈ right})
    (fun z =>
      finsetMobiusResponse fullPacket
        (fun active =>
          branch (restrictInteractionPacket active z)))
      =ᶠ[𝓝 0]
        (fun _ :
          (Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) =>
          (0 : ℂ)) := by
  dsimp only
  obtain ⟨totalBranch, htotalAnalytic, htotal0, htotalRoot, hcross⟩ :=
    L.exists_disconnectedLocalBranch_crossPacket_eq_zero
      onsite hinj left right hleft hright hdisj x
  let P :=
    Sum {e : E // e ∈ left} {e : E // e ∈ right}
  let H : (P → ℂ) → Matrix (∀ v, A v) (∀ v, A v) ℂ :=
    affineMatrixFamily
      (Matrix.diagonal (onsiteProductEnergy onsite))
      (L.splitPacketGlobalInteraction left right)
  have hmatrix :
      Tendsto H (𝓝 0) (𝓝 (Matrix.diagonal (onsiteProductEnergy onsite))) := by
    have ha :=
      affineMatrixFamily_analyticAt
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (L.splitPacketGlobalInteraction left right) 0
    have hzero : H 0 = Matrix.diagonal (onsiteProductEnergy onsite) := by
      simp [H, affineMatrixFamily]
    have hc := ha.continuousAt
    change Tendsto H (𝓝 0) (𝓝 (H 0)) at hc
    rw [hzero] at hc
    exact hc
  have hbranchTendsto :
      Tendsto branch (𝓝 0) (𝓝 (onsiteProductEnergy onsite x)) := by
    have hc := hbranch.continuousAt
    change Tendsto branch (𝓝 0) (𝓝 (branch 0)) at hc
    rw [hbranch0] at hc
    exact hc
  have htotalTendsto :
      Tendsto totalBranch (𝓝 0) (𝓝 (onsiteProductEnergy onsite x)) := by
    have hc := htotalAnalytic.continuousAt
    change Tendsto totalBranch (𝓝 0) (𝓝 (totalBranch 0)) at hc
    rw [htotal0] at hc
    exact hc
  have hgerm :
      branch =ᶠ[𝓝 0] totalBranch :=
    simpleDiagonalMatrix_root_germs_unique
      (onsiteProductEnergy onsite) hinj x
      hmatrix hbranchTendsto htotalTendsto hbranchRoot htotalRoot
  let fullPacket : Finset P :=
    (Finset.univ : Finset {e : E // e ∈ left}).map
        (sumInlEmbedding {e : E // e ∈ left} {e : E // e ∈ right}) ∪
      (Finset.univ : Finset {e : E // e ∈ right}).map
        (sumInrEmbedding {e : E // e ∈ left} {e : E // e ∈ right})
  have hactive :
      ∀ active : Finset P,
        (fun z => branch (restrictInteractionPacket active z))
          =ᶠ[𝓝 0]
        (fun z => totalBranch (restrictInteractionPacket active z)) := by
    intro active
    have htendsto :
        Tendsto (restrictInteractionPacket active)
          (𝓝 (0 : P → ℂ)) (𝓝 (0 : P → ℂ)) := by
      have ha := restrictInteractionPacket_analyticAt active
      have hzero :
          restrictInteractionPacket active (0 : P → ℂ) = 0 := by
        funext e
        simp [restrictInteractionPacket]
      have hc := ha.continuousAt
      change Tendsto (restrictInteractionPacket active) (𝓝 0)
        (𝓝 (restrictInteractionPacket active 0)) at hc
      rw [hzero] at hc
      exact hc
    exact hgerm.comp_tendsto htendsto
  have hall :
      ∀ᶠ z : P → ℂ in 𝓝 0,
        ∀ active ∈ Finset.Iic fullPacket,
          branch (restrictInteractionPacket active z) =
            totalBranch (restrictInteractionPacket active z) := by
    rw [Finset.eventually_all]
    intro active hactiveMem
    exact hactive active
  filter_upwards [hall] with z hz
  change finsetMobiusResponse fullPacket
      (fun active => branch (restrictInteractionPacket active z)) = 0
  have heq : finsetMobiusResponse fullPacket
      (fun active => branch (restrictInteractionPacket active z)) =
      finsetMobiusResponse fullPacket
        (fun active => totalBranch (restrictInteractionPacket active z)) := by
    unfold finsetMobiusResponse
    apply Finset.sum_congr rfl
    intro active hactiveMem
    congr 1
    exact hz (fullPacket \ active)
      (Finset.mem_Iic.mpr
        (Finset.sdiff_subset : fullPacket \ active ⊆ fullPacket))
  rw [heq]
  exact hcross z

/-- Incidence-algebra form of branch-independent disconnected cancellation. -/
theorem disconnectedLocalBranch_crossPacket_posetMobius_germ_eq_zero
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : Finset E)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    (x : ∀ v, A v)
    (branch :
      (Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbranch0 : branch 0 = onsiteProductEnergy onsite x)
    (hbranchRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (L.splitPacketGlobalInteraction left right)
            coupling,
            branch coupling) = 0) :
    let fullPacket :=
      (Finset.univ : Finset {e : E // e ∈ left}).map
          (sumInlEmbedding {e : E // e ∈ left} {e : E // e ∈ right}) ∪
        (Finset.univ : Finset {e : E // e ∈ right}).map
          (sumInrEmbedding {e : E // e ∈ left} {e : E // e ∈ right})
    (fun z =>
      posetMobiusProbe (R := ℂ) fullPacket
        (fun active =>
          branch (restrictInteractionPacket active z)))
      =ᶠ[𝓝 0]
        (fun _ :
          (Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) =>
          (0 : ℂ)) := by
  dsimp only
  have hfin := L.disconnectedLocalBranch_crossPacket_germ_eq_zero
    onsite hinj left right hleft hright hdisj x branch
    hbranch hbranch0 hbranchRoot
  filter_upwards [hfin] with z hz
  rw [← finsetMobiusResponse_eq_posetMobiusProbe]
  exact hz

/-- **All-order disconnected cancellation.**  Along every scalar coupling
direction, every Taylor jet of the full mixed response between two disjoint
site sectors is zero. -/
theorem disconnectedLocalBranch_crossPacket_iteratedDeriv_eq_zero
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : Finset E)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    (x : ∀ v, A v)
    (branch :
      (Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbranch0 : branch 0 = onsiteProductEnergy onsite x)
    (hbranchRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (L.splitPacketGlobalInteraction left right)
            coupling,
            branch coupling) = 0)
    (z : Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ)
    (n : ℕ) :
    let fullPacket :=
      (Finset.univ : Finset {e : E // e ∈ left}).map
          (sumInlEmbedding {e : E // e ∈ left} {e : E // e ∈ right}) ∪
        (Finset.univ : Finset {e : E // e ∈ right}).map
          (sumInrEmbedding {e : E // e ∈ left} {e : E // e ∈ right})
    iteratedDeriv n
      (fun g : ℂ =>
        finsetMobiusResponse fullPacket
          (fun active =>
            branch (restrictInteractionPacket active (g • z)))) 0 = 0 := by
  dsimp only
  have hgerm := L.disconnectedLocalBranch_crossPacket_germ_eq_zero
    onsite hinj left right hleft hright hdisj x branch
    hbranch hbranch0 hbranchRoot
  let ray :
      ℂ →
        (Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) :=
    fun g => g • z
  have hray : Tendsto ray (𝓝 0) (𝓝 0) := by
    have hc : Continuous ray := continuous_id.smul continuous_const
    have hc0 : ContinuousAt ray 0 := hc.continuousAt
    change Tendsto ray (𝓝 0) (𝓝 (ray 0)) at hc0
    simpa only [ray, zero_smul] using hc0
  have hpull := hgerm.comp_tendsto hray
  have heq :
      (fun g : ℂ =>
        finsetMobiusResponse
          ((Finset.univ : Finset {e : E // e ∈ left}).map
              (sumInlEmbedding {e : E // e ∈ left}
                {e : E // e ∈ right}) ∪
            (Finset.univ : Finset {e : E // e ∈ right}).map
              (sumInrEmbedding {e : E // e ∈ left}
                {e : E // e ∈ right}))
          (fun active =>
            branch (restrictInteractionPacket active (g • z))))
        =ᶠ[𝓝 0] (fun _ : ℂ => (0 : ℂ)) := by
    simpa only [Function.comp_apply, ray] using hpull
  rw [Filter.EventuallyEq.iteratedDeriv_eq n heq]
  simp

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
