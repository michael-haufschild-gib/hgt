import GaloisForLFunctions.HTGeometry.LocalSpectralPacketGerm

/-!
# Spectator locality of active-packet eigenvalue germs

For two product configurations agreeing on every site touched by an active interaction packet, the
corresponding restricted simple-eigenvalue branches differ only by the constant onsite spectator
energy. Therefore every positive-order packet jet is genuinely local on the packet's incident
sites. This proves locality for actual finite local matrix generators, not for an abstract cluster
ansatz.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

omit [Fintype V] [DecidableEq V]
    [(v : V) → Fintype (A v)] [(v : V) → DecidableEq (A v)] in
theorem restrictLocalConfiguration_eq_of_eqOn
    (S : Finset V) {x y : ∀ v, A v}
    (hxy : ∀ v ∈ S, x v = y v) :
    restrictLocalConfiguration S x = restrictLocalConfiguration S y := by
  funext v
  exact hxy v.1 v.2

/-- **Actual spectral packet locality.** Restricted branches born from configurations agreeing on
the packet's site support differ, as germs, by exactly their constant spectator onsite-energy
difference. -/
theorem restrictedBranches_difference_germ_eq_spectatorDifference
    [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    {x y : ∀ v, A v}
    (branchX branchY : (E → ℂ) → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbranchX0 : branchX 0 = onsiteProductEnergy onsite x)
    (hbranchY0 : branchY 0 = onsiteProductEnergy onsite y)
    (hbranchXRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            branchX coupling) = 0)
    (hbranchYRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            branchY coupling) = 0)
    (packet : Finset E)
    (hxy : ∀ v ∈ L.packetSiteSupport packet, x v = y v) :
    (fun coupling =>
      branchX (extendCouplingFromPacket packet coupling) -
        branchY (extendCouplingFromPacket packet coupling))
      =ᶠ[𝓝 0]
    (fun _ =>
      outsideOnsiteEnergy onsite (L.packetSiteSupport packet)
          (restrictOutsideConfiguration (L.packetSiteSupport packet) x) -
        outsideOnsiteEnergy onsite (L.packetSiteSupport packet)
          (restrictOutsideConfiguration (L.packetSiteSupport packet) y)) := by
  obtain ⟨localX, packetX, hlocalXa, hpacketXa, hlocalX0,
      hpacketX0, hlocalXRoot, hpacketXRoot, hsplitX, hgermX⟩ :=
    L.fullBranch_restrictedToPacket_germ_eq_packetBranch
      onsite hinj x branchX hbranchX hbranchX0 hbranchXRoot packet
  obtain ⟨localY, packetY, hlocalYa, hpacketYa, hlocalY0,
      hpacketY0, hlocalYRoot, hpacketYRoot, hsplitY, hgermY⟩ :=
    L.fullBranch_restrictedToPacket_germ_eq_packetBranch
      onsite hinj y branchY hbranchY hbranchY0 hbranchYRoot packet
  let U := L.packetSiteSupport packet
  have hlocalConfig :
      restrictLocalConfiguration U x = restrictLocalConfiguration U y :=
    restrictLocalConfiguration_eq_of_eqOn U hxy
  have hlocalBase :
      localOnsiteEnergy onsite U (restrictLocalConfiguration U x) =
        localOnsiteEnergy onsite U (restrictLocalConfiguration U y) := by
    rw [hlocalConfig]
  have hinjLocal :
      Function.Injective (localOnsiteEnergy onsite U) :=
    localOnsiteEnergy_injective_of_product onsite hinj U
  have hmatrix :
      Tendsto
        (affineMatrixFamily
          (Matrix.diagonal (localOnsiteEnergy onsite U))
          (L.packetLocalInteraction packet))
        (𝓝 0)
        (𝓝 (Matrix.diagonal (localOnsiteEnergy onsite U))) := by
    have ha :=
      affineMatrixFamily_analyticAt
        (Matrix.diagonal (localOnsiteEnergy onsite U))
        (L.packetLocalInteraction packet) 0
    have hzero :
        affineMatrixFamily
          (Matrix.diagonal (localOnsiteEnergy onsite U))
          (L.packetLocalInteraction packet) 0 =
        Matrix.diagonal (localOnsiteEnergy onsite U) := by
      simp [affineMatrixFamily]
    have hc := ha.continuousAt
    change Tendsto
      (affineMatrixFamily
        (Matrix.diagonal (localOnsiteEnergy onsite U))
        (L.packetLocalInteraction packet))
      (𝓝 0)
      (𝓝 (affineMatrixFamily
        (Matrix.diagonal (localOnsiteEnergy onsite U))
        (L.packetLocalInteraction packet) 0)) at hc
    rw [hzero] at hc
    exact hc
  have hlocalXTendsto :
      Tendsto localX (𝓝 0)
        (𝓝 (localOnsiteEnergy onsite U
          (restrictLocalConfiguration U x))) := by
    have hc := hlocalXa.continuousAt
    change Tendsto localX (𝓝 0) (𝓝 (localX 0)) at hc
    rw [hlocalX0] at hc
    exact hc
  have hlocalYTendsto :
      Tendsto localY (𝓝 0)
        (𝓝 (localOnsiteEnergy onsite U
          (restrictLocalConfiguration U x))) := by
    have hc := hlocalYa.continuousAt
    change Tendsto localY (𝓝 0) (𝓝 (localY 0)) at hc
    rw [hlocalY0, ← hlocalBase] at hc
    exact hc
  have hlocalGerm :
      localX =ᶠ[𝓝 0] localY :=
    simpleDiagonalMatrix_root_germs_unique
      (localOnsiteEnergy onsite U) hinjLocal
      (restrictLocalConfiguration U x)
      hmatrix hlocalXTendsto hlocalYTendsto hlocalXRoot hlocalYRoot
  rw [hsplitX] at hgermX
  rw [hsplitY] at hgermY
  filter_upwards [hgermX, hgermY, hlocalGerm] with coupling hx hy hlocal
  rw [hx, hy, hlocal]
  ring

/-- Every positive-order active-packet eigenvalue jet is local on the packet's incident sites. -/
theorem restrictedBranches_iteratedFDeriv_eq_of_positive
    [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    {x y : ∀ v, A v}
    (branchX branchY : (E → ℂ) → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbranchX0 : branchX 0 = onsiteProductEnergy onsite x)
    (hbranchY0 : branchY 0 = onsiteProductEnergy onsite y)
    (hbranchXRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            branchX coupling) = 0)
    (hbranchYRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            branchY coupling) = 0)
    (packet : Finset E)
    (hxy : ∀ v ∈ L.packetSiteSupport packet, x v = y v)
    {n : ℕ} (hn : n ≠ 0) :
    iteratedFDeriv ℂ n
        (fun coupling =>
          branchX (extendCouplingFromPacket packet coupling)) 0 =
      iteratedFDeriv ℂ n
        (fun coupling =>
          branchY (extendCouplingFromPacket packet coupling)) 0 := by
  have hdiff :=
    L.restrictedBranches_difference_germ_eq_spectatorDifference
      onsite hinj branchX branchY hbranchX hbranchY
      hbranchX0 hbranchY0 hbranchXRoot hbranchYRoot packet hxy
  have hAt := (hdiff.iteratedFDeriv ℂ n).eq_of_nhds
  have hext := extendCouplingFromPacket_analyticAt (E := E) packet
  have hext0 :
      extendCouplingFromPacket packet
        (0 : {e : E // e ∈ packet} → ℂ) = 0 := by
    funext e
    simp [extendCouplingFromPacket]
  have hXa :
      AnalyticAt ℂ
        (fun coupling =>
          branchX (extendCouplingFromPacket packet coupling)) 0 :=
    hbranchX.comp_of_eq' hext hext0
  have hYa :
      AnalyticAt ℂ
        (fun coupling =>
          branchY (extendCouplingFromPacket packet coupling)) 0 :=
    hbranchY.comp_of_eq' hext hext0
  change iteratedFDeriv ℂ n
      ((fun coupling =>
        branchX (extendCouplingFromPacket packet coupling)) -
       (fun coupling =>
        branchY (extendCouplingFromPacket packet coupling))) 0 =
    _ at hAt
  rw [iteratedFDeriv_sub_apply hXa.contDiffAt hYa.contDiffAt,
    iteratedFDeriv_const_of_ne hn] at hAt
  exact sub_eq_zero.mp hAt

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
