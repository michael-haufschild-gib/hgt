import GaloisForLFunctions.HTGeometry.LocalSpectralObserverDirectSumLaw

/-!
# Universal connected-sector law for linear spectral observers

The site-Möbius observer is only one member of a much larger class.  This file
proves the same connected-packet law for every continuous linear functional on
the full vector of product-state eigenvalue shifts.

Every such observer response has a unique orthogonal interaction-packet
decomposition.  Disconnected packets vanish as germs, and a packet containing
`n` independently switchable interaction channels contributes only at order
`O (‖g‖ ^ n)`.  The response is nonzero exactly when one connected packet
sector is nonzero.  Energy gaps and higher site contrasts are explicit
specializations of this universal observer.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- Vector of interaction-induced simple spectral shifts over all product
configurations. -/
noncomputable def productSpectralInteractionShiftVector
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (z : E → ℂ) : ((∀ v, A v) → ℂ) :=
  fun config => L.productSpectralInteractionShift onsite hinj config z

/-- Response of an arbitrary continuous linear spectral observer. -/
noncomputable def linearSpectralObserverResponse
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ)
    (z : E → ℂ) : ℂ :=
  observer (L.productSpectralInteractionShiftVector onsite hinj z)

omit [∀ v, Nonempty (A v)] in
/-- The complete product spectral-shift vector is analytic at zero
coupling. -/
theorem productSpectralInteractionShiftVector_analyticAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite)) :
    AnalyticAt ℂ
      (L.productSpectralInteractionShiftVector onsite hinj) 0 := by
  apply AnalyticAt.pi
  intro config
  exact
    (L.productEigenvalueBranch_spec onsite hinj config).1.sub
      analyticAt_const

omit [∀ v, Nonempty (A v)] in
/-- Every continuous linear spectral-observer response is analytic. -/
theorem linearSpectralObserverResponse_analyticAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ) :
    AnalyticAt ℂ
      (L.linearSpectralObserverResponse onsite hinj observer) 0 := by
  have h :=
    (observer.analyticAt
      (L.productSpectralInteractionShiftVector onsite hinj 0)).comp
        (L.productSpectralInteractionShiftVector_analyticAt onsite hinj)
  simpa [linearSpectralObserverResponse, Function.comp_def] using h

/-- Irreducible interaction-packet sector of a linear observer response. -/
noncomputable def linearSpectralObserverPacketResponse
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ)
    (packet : Finset E) (z : E → ℂ) : ℂ :=
  spectralPacketResponse
    (L.linearSpectralObserverResponse onsite hinj observer) packet z

omit [∀ v, Nonempty (A v)] in
/-- On a nonempty packet, applying the observer commutes exactly with taking
the packet sector. -/
theorem linearSpectralObserverPacketResponse_eq
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ)
    (packet : Finset E) (hpacket : packet.Nonempty) (z : E → ℂ) :
    L.linearSpectralObserverPacketResponse onsite hinj observer packet z =
      observer (fun config =>
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj config) packet z) := by
  unfold linearSpectralObserverPacketResponse
  unfold spectralPacketResponse finsetMobiusResponse
  unfold linearSpectralObserverResponse productSpectralInteractionShiftVector
  rw [show
      (∑ d ∈ packet.powerset,
        (-1 : ℂ) ^ d.card *
          observer (fun config =>
            L.productSpectralInteractionShift onsite hinj config
              (restrictInteractionPacket (packet \ d) z))) =
      observer
        (∑ d ∈ packet.powerset,
          (-1 : ℂ) ^ d.card •
            (fun config =>
              L.productSpectralInteractionShift onsite hinj config
                (restrictInteractionPacket (packet \ d) z))) by
    simp]
  apply congrArg observer
  funext config
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold productSpectralInteractionShift
  have hconst :
      ∑ d ∈ packet.powerset,
        (-1 : ℂ) ^ d.card *
          onsiteProductEnergy onsite config = 0 := by
    obtain ⟨e, he⟩ := hpacket
    have hz :
        finsetMobiusResponse packet
          (fun _ : Finset E => onsiteProductEnergy onsite config) = 0 := by
      apply finsetMobiusResponse_eq_zero_of_insert_invariant he
      intro active
      rfl
    exact hz
  simp only [mul_sub, Finset.sum_sub_distrib, hconst, sub_zero]

omit [∀ v, Nonempty (A v)] in
/-- Every `n`-channel observer packet is delayed to at least order `n`. -/
theorem linearSpectralObserverPacketResponse_couplingRay_isBigO
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ)
    (packet : Finset E) (z : E → ℂ) :
    (fun g : ℂ =>
      L.linearSpectralObserverPacketResponse onsite hinj
        observer packet (g • z))
      =O[𝓝 0] fun g : ℂ => ‖g‖ ^ packet.card := by
  exact spectralPacketResponse_couplingRay_isBigO
    (L.linearSpectralObserverResponse onsite hinj observer)
    (L.linearSpectralObserverResponse_analyticAt onsite hinj observer)
    z packet

omit [Fintype E] [∀ v, Nonempty (A v)] in
/-- A spatially disconnected packet is necessarily nonempty. -/
theorem SpatiallyDisconnectedPacket.nonempty
    {L : FiniteLocalInteractionFamily V E A}
    {packet : Finset E}
    (hpacket : SpatiallyDisconnectedPacket L packet) :
    packet.Nonempty := by
  obtain ⟨left, right, hdisjoint, hleft, hright, hunion, hsite⟩ :=
    hpacket
  rw [← hunion]
  exact hleft.mono (Finset.subset_union_left)

/-- Every spatially disconnected packet is invisible to every continuous
linear spectral observer. -/
theorem linearSpectralObserverPacketResponse_germ_eq_zero_of_disconnected
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ)
    (packet : Finset E)
    (hpacket : SpatiallyDisconnectedPacket L packet) :
    L.linearSpectralObserverPacketResponse onsite hinj observer packet
      =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) := by
  have hconfig : ∀ config : ∀ v, A v,
      spectralPacketResponse
        (L.productEigenvalueBranch onsite hinj config) packet
        =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) := by
    intro config
    have hs := L.productEigenvalueBranch_spec onsite hinj config
    exact
      L.globalBranch_spectralPacketResponse_germ_eq_zero_of_disconnected
        onsite hinj config
        (L.productEigenvalueBranch onsite hinj config)
        hs.1 hs.2.1 hs.2.2 packet hpacket
  have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
      ∀ config ∈ (Finset.univ : Finset (∀ v, A v)),
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj config) packet z = 0 := by
    rw [Finset.eventually_all]
    intro config hconfigMem
    exact hconfig config
  filter_upwards [hall] with z hz
  rw [L.linearSpectralObserverPacketResponse_eq onsite hinj observer
    packet hpacket.nonempty z]
  have hzero :
      (fun config =>
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj config) packet z) =
        (0 : (∀ v, A v) → ℂ) := by
    funext config
    exact hz config (Finset.mem_univ config)
  rw [hzero, map_zero]

omit [∀ v, Nonempty (A v)] in
/-- Every linear observer response is exactly the sum of its nonempty packet
sectors. -/
theorem linearSpectralObserverResponse_eq_sum_nonemptyPackets
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ)
    (z : E → ℂ) :
    L.linearSpectralObserverResponse onsite hinj observer z =
      ∑ packet ∈ (Finset.univ : Finset (Finset E)).erase ∅,
        L.linearSpectralObserverPacketResponse onsite hinj
          observer packet z := by
  have hall :=
    sum_spectralPacketResponse_eq_branch
      (L.linearSpectralObserverResponse onsite hinj observer) z
  have hzero :
      L.linearSpectralObserverResponse onsite hinj observer 0 = 0 := by
    unfold linearSpectralObserverResponse
    have hvector :
        L.productSpectralInteractionShiftVector onsite hinj 0 = 0 := by
      funext config
      unfold productSpectralInteractionShiftVector
      unfold productSpectralInteractionShift
      rw [(L.productEigenvalueBranch_spec onsite hinj config).2.1]
      simp
    rw [hvector, map_zero]
  have hempty :
      L.linearSpectralObserverPacketResponse onsite hinj observer ∅ z = 0 := by
    unfold linearSpectralObserverPacketResponse
    rw [spectralPacketResponse_empty, hzero]
  rw [← hall]
  change (∑ packet ∈ (Finset.univ : Finset (Finset E)),
      L.linearSpectralObserverPacketResponse onsite hinj
        observer packet z) = _
  rw [← Finset.sum_erase_add
    (Finset.univ : Finset (Finset E))
    (fun packet =>
      L.linearSpectralObserverPacketResponse onsite hinj
        observer packet z)
    (Finset.mem_univ (∅ : Finset E))]
  rw [hempty, add_zero]

/-- All nonempty spatially indecomposable interaction packets. -/
noncomputable def observerConnectedPackets
    (L : FiniteLocalInteractionFamily V E A) :
    Finset (Finset E) := by
  classical
  exact (Finset.univ : Finset (Finset E)).filter
    (fun packet => packet.Nonempty ∧
      ¬SpatiallyDisconnectedPacket L packet)

/-- **Universal connected-packet observer decomposition.**  Near zero
coupling, every continuous linear spectral observer is exactly the sum of its
nonempty spatially indecomposable packet sectors. -/
theorem linearSpectralObserverResponse_eq_sum_connectedPackets_germ
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ) :
    L.linearSpectralObserverResponse onsite hinj observer =ᶠ[𝓝 0]
      (fun z =>
        ∑ packet ∈ observerConnectedPackets L,
          L.linearSpectralObserverPacketResponse onsite hinj
            observer packet z) := by
  classical
  let nonemptyPackets := (Finset.univ : Finset (Finset E)).erase ∅
  let disconnectedPackets :=
    nonemptyPackets \ observerConnectedPackets L
  have hzero : ∀ packet ∈ disconnectedPackets,
      L.linearSpectralObserverPacketResponse onsite hinj observer packet
        =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) := by
    intro packet hpacket
    have hmemNon := (Finset.mem_sdiff.mp hpacket).1
    have hne : packet ≠ ∅ := by
      simpa [nonemptyPackets] using hmemNon
    have hpnonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hnot := (Finset.mem_sdiff.mp hpacket).2
    have hdisc : SpatiallyDisconnectedPacket L packet := by
      by_contra hn
      exact hnot (by
        simp [observerConnectedPackets, hpnonempty, hn])
    exact
      L.linearSpectralObserverPacketResponse_germ_eq_zero_of_disconnected
        onsite hinj observer packet hdisc
  have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
      ∀ packet ∈ disconnectedPackets,
        L.linearSpectralObserverPacketResponse onsite hinj
          observer packet z = 0 := by
    rw [Finset.eventually_all]
    intro packet hpacket
    exact hzero packet hpacket
  filter_upwards [hall] with z hz
  rw [L.linearSpectralObserverResponse_eq_sum_nonemptyPackets
    onsite hinj observer z]
  symm
  apply Finset.sum_subset
  · intro packet hpacket
    have hp := (Finset.mem_filter.mp hpacket).2.1
    exact Finset.mem_erase.mpr
      ⟨Finset.Nonempty.ne_empty hp, Finset.mem_univ _⟩
  · intro packet hpacket hnot
    exact hz packet (Finset.mem_sdiff.mpr ⟨hpacket, hnot⟩)

/-- A linear observer response vanishes exactly when every connected packet
sector vanishes. -/
theorem linearSpectralObserverResponse_germ_eq_zero_iff
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ) :
    L.linearSpectralObserverResponse onsite hinj observer
        =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) ↔
      ∀ packet,
        packet.Nonempty →
        ¬SpatiallyDisconnectedPacket L packet →
        L.linearSpectralObserverPacketResponse onsite hinj observer packet
          =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) := by
  classical
  constructor
  · intro hzero packet hnonempty hconnected
    have hp := spectralPacketResponse_congr_germ hzero packet
    change spectralPacketResponse
      (L.linearSpectralObserverResponse onsite hinj observer) packet
        =ᶠ[𝓝 0] (fun _ : E → ℂ => 0)
    filter_upwards [hp] with z hz
    rw [hz]
    simp [spectralPacketResponse, finsetMobiusResponse]
  · intro hpackets
    have hdecomp :=
      L.linearSpectralObserverResponse_eq_sum_connectedPackets_germ
        onsite hinj observer
    have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
        ∀ packet ∈ observerConnectedPackets L,
          L.linearSpectralObserverPacketResponse onsite hinj
            observer packet z = 0 := by
      rw [Finset.eventually_all]
      intro packet hpacket
      have hp := (Finset.mem_filter.mp hpacket).2
      exact hpackets packet hp.1 hp.2
    filter_upwards [hdecomp, hall] with z hz hpacketZero
    rw [hz]
    apply Finset.sum_eq_zero
    intro packet hpacket
    exact hpacketZero packet hpacket

/-- **Universal linear-observer visibility law.**  A continuous linear
spectral observer has a nonzero interaction-induced germ exactly when some
nonempty spatially indecomposable packet has a nonzero irreducible observer
response. -/
theorem linearSpectralObserverResponse_germ_ne_zero_iff
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ) :
    ¬L.linearSpectralObserverResponse onsite hinj observer
        =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) ↔
      ∃ packet,
        packet.Nonempty ∧
        ¬SpatiallyDisconnectedPacket L packet ∧
        ¬L.linearSpectralObserverPacketResponse onsite hinj observer packet
          =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) := by
  constructor
  · intro hvisible
    by_contra hnoPacket
    push Not at hnoPacket
    exact hvisible
      ((L.linearSpectralObserverResponse_germ_eq_zero_iff
        onsite hinj observer).2 hnoPacket)
  · rintro ⟨packet, hnonempty, hconnected, hpacketVisible⟩ hzero
    exact hpacketVisible
      ((L.linearSpectralObserverResponse_germ_eq_zero_iff
        onsite hinj observer).1 hzero packet hnonempty hconnected)

/-- Continuous linear observer extracting one energy difference. -/
noncomputable def spectralGapObserver
    (left right : ∀ v, A v) :
    ((∀ v, A v) → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : (∀ v, A v) => ℂ) left) -
  (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : (∀ v, A v) => ℂ) right)

omit [Fintype V] [DecidableEq V]
  [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
  [∀ v, Nonempty (A v)] in
@[simp]
theorem spectralGapObserver_apply
    (left right : ∀ v, A v)
    (energy : (∀ v, A v) → ℂ) :
    spectralGapObserver left right energy =
      energy left - energy right := by
  rfl

omit [∀ v, Nonempty (A v)] in
/-- Every interaction-induced energy gap is a specialization of the universal
linear spectral-observer response. -/
theorem linearSpectralObserverResponse_spectralGapObserver
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : ∀ v, A v) (z : E → ℂ) :
    L.linearSpectralObserverResponse onsite hinj
        (spectralGapObserver left right) z =
      L.productSpectralInteractionShift onsite hinj left z -
        L.productSpectralInteractionShift onsite hinj right z := by
  rfl

/-- Continuous linear observer implementing a higher Boolean site
contrast. -/
noncomputable def siteMobiusSpectralObserver
    (x alternative : ∀ v, A v) (sites : Finset V) :
    ((∀ v, A v) → ℂ) →L[ℂ] ℂ :=
  ∑ d ∈ sites.powerset,
    ((-1 : ℂ) ^ d.card) •
      ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : (∀ v, A v) => ℂ)
        (dependentUpdateOnFinset x alternative (sites \ d))

omit [Fintype V] [∀ v, Fintype (A v)]
  [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)] in
@[simp]
theorem siteMobiusSpectralObserver_apply
    (x alternative : ∀ v, A v) (sites : Finset V)
    (energy : (∀ v, A v) → ℂ) :
    siteMobiusSpectralObserver x alternative sites energy =
      dependentHigherCoordinateContrast x alternative sites energy := by
  unfold siteMobiusSpectralObserver dependentHigherCoordinateContrast
  unfold finsetMobiusResponse
  simp

omit [∀ v, Nonempty (A v)] in
/-- Higher site contrasts are exactly the site-Möbius specialization of the
universal linear spectral-observer response. -/
theorem linearSpectralObserverResponse_siteMobiusSpectralObserver
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ) :
    L.linearSpectralObserverResponse onsite hinj
        (siteMobiusSpectralObserver x alternative sites) z =
      L.productSpectralInteractionShiftSiteContrast onsite hinj
        x alternative sites z := by
  unfold linearSpectralObserverResponse
  rw [siteMobiusSpectralObserver_apply]
  rfl

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
