import GaloisForLFunctions.HTGeometry.LocalSpectralObserverSteinerLaw

/-!
# Direct connected-sector law for observer-visible spectral time

Boolean interaction-packet responses are pairwise orthogonal projections.
Consequently distinct spatial packets cannot cancel one another as germs.
Combining this algebraic fact with the observer Steiner decomposition gives
an exact visibility criterion: an observer contrast is nonzero precisely when
at least one spatially indecomposable packet spanning every queried site has a
nonzero irreducible response.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

/-- Successive coordinate restrictions intersect their active packets. -/
theorem restrictInteractionPacket_comp
    {E R : Type*} [DecidableEq E] [Zero R]
    (left right : Finset E) (z : E → R) :
    restrictInteractionPacket left
        (restrictInteractionPacket right z) =
      restrictInteractionPacket (left ∩ right) z := by
  funext e
  by_cases hl : e ∈ left <;> by_cases hr : e ∈ right <;>
    simp [restrictInteractionPacket, hl, hr]

/-- A packet response vanishes after restricting away any required packet
coordinate, and is unchanged after retaining all of them. -/
theorem spectralPacketResponse_restrictInteractionPacket
    {E : Type*} [Fintype E] [DecidableEq E]
    (branch : (E → ℂ) → ℂ)
    (packet active : Finset E) (z : E → ℂ) :
    spectralPacketResponse branch packet
        (restrictInteractionPacket active z) =
      if packet ⊆ active then
        spectralPacketResponse branch packet z
      else 0 := by
  by_cases hsub : packet ⊆ active
  · rw [if_pos hsub]
    unfold spectralPacketResponse finsetMobiusResponse
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    apply congrArg branch
    rw [restrictInteractionPacket_comp]
    have hinter : (packet \ d) ∩ active = packet \ d :=
      Finset.inter_eq_left.mpr (Finset.sdiff_subset.trans hsub)
    rw [hinter]
  · rw [if_neg hsub]
    obtain ⟨e, hepacket, heactive⟩ := Finset.not_subset.mp hsub
    unfold spectralPacketResponse
    apply finsetMobiusResponse_eq_zero_of_insert_invariant hepacket
    intro selected
    apply congrArg branch
    rw [restrictInteractionPacket_comp, restrictInteractionPacket_comp]
    apply congrArg (fun s => restrictInteractionPacket s z)
    ext i
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hie | his, hia⟩
      · exact False.elim (heactive (hie ▸ hia))
      · exact ⟨his, hia⟩
    · rintro ⟨his, hia⟩
      exact ⟨Or.inr his, hia⟩

/-- **Packet-projector orthogonality.**  Applying the `query` packet
projector to the `packet` sector returns that sector when the labels agree
and zero otherwise. -/
theorem spectralPacketResponse_spectralPacketResponse
    {E : Type*} [Fintype E] [DecidableEq E]
    (branch : (E → ℂ) → ℂ)
    (packet query : Finset E) (z : E → ℂ) :
    spectralPacketResponse
        (spectralPacketResponse branch packet) query z =
      if packet = query then
        spectralPacketResponse branch packet z
      else 0 := by
  change finsetMobiusResponse query
      (fun active =>
        spectralPacketResponse branch packet
          (restrictInteractionPacket active z)) = _
  rw [show
      (fun active =>
        spectralPacketResponse branch packet
          (restrictInteractionPacket active z)) =
      (fun active =>
        booleanZetaFeature (R := ℂ) packet active *
          spectralPacketResponse branch packet z) by
    funext active
    rw [spectralPacketResponse_restrictInteractionPacket]
    simp [booleanZetaFeature, IncidenceAlgebra.zeta_apply]]
  let c := spectralPacketResponse branch packet z
  rw [show
      (fun active => booleanZetaFeature (R := ℂ) packet active * c) =
        c • booleanZetaFeature (R := ℂ) packet by
    funext active
    simp [mul_comm]]
  change finsetMobiusResponseLinear query
      (c • booleanZetaFeature (R := ℂ) packet) =
    if packet = query then c else 0
  rw [map_smul, finsetMobiusResponseLinear_apply,
    finsetMobiusResponse_booleanZetaFeature]
  split_ifs
  · simp
  · simp

/-- Boolean Möbius probes on two independent finite coordinate sets
commute. -/
theorem finsetMobiusResponse_comm
    {I J R : Type*} [DecidableEq I] [DecidableEq J] [CommRing R]
    (left : Finset I) (right : Finset J)
    (f : Finset I → Finset J → R) :
    finsetMobiusResponse left
        (fun a => finsetMobiusResponse right (f a)) =
      finsetMobiusResponse right
        (fun b => finsetMobiusResponse left (fun a => f a b)) := by
  unfold finsetMobiusResponse
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- A nonempty packet projector kills an additive constant. -/
theorem spectralPacketResponse_sub_const_of_nonempty
    {E : Type*} [Fintype E] [DecidableEq E]
    (branch : (E → ℂ) → ℂ) (constant : ℂ)
    (packet : Finset E) (hpacket : packet.Nonempty) (z : E → ℂ) :
    spectralPacketResponse (fun w => branch w - constant) packet z =
      spectralPacketResponse branch packet z := by
  obtain ⟨e, he⟩ := hpacket
  have hconst :
      finsetMobiusResponse packet (fun _ : Finset E => constant) = 0 := by
    apply finsetMobiusResponse_eq_zero_of_insert_invariant he
    intro active
    rfl
  change finsetMobiusResponseLinear packet
      ((fun active => branch (restrictInteractionPacket active z)) -
        (fun _ : Finset E => constant)) =
    spectralPacketResponse branch packet z
  rw [map_sub, finsetMobiusResponseLinear_apply,
    finsetMobiusResponseLinear_apply, hconst, sub_zero]
  rfl

/-- Packet projection preserves equality of germs at zero coupling. -/
theorem spectralPacketResponse_congr_germ
    {E : Type*} [Fintype E] [DecidableEq E]
    {left right : (E → ℂ) → ℂ}
    (h : left =ᶠ[𝓝 0] right) (packet : Finset E) :
    spectralPacketResponse left packet =ᶠ[𝓝 0]
      spectralPacketResponse right packet := by
  have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
      ∀ active ∈ Finset.Iic packet,
        left (restrictInteractionPacket active z) =
          right (restrictInteractionPacket active z) := by
    rw [Finset.eventually_all]
    intro active hactive
    have ha := (restrictInteractionPacket_analyticAt active).continuousAt
    have hzero :
        restrictInteractionPacket active (0 : E → ℂ) = 0 := by
      funext e
      simp [restrictInteractionPacket]
    change Tendsto (restrictInteractionPacket active) (𝓝 0)
      (𝓝 (restrictInteractionPacket active 0)) at ha
    rw [hzero] at ha
    exact h.comp_tendsto ha
  filter_upwards [hall] with z hz
  unfold spectralPacketResponse finsetMobiusResponse
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  exact hz (packet \ d) (Finset.mem_Iic.mpr Finset.sdiff_subset)

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

omit [∀ v, Nonempty (A v)] in
/-- Interaction-packet projection commutes with the observer site contrast;
the nonempty packet also removes the onsite constant. -/
theorem spectralPacketResponse_productSpectralInteractionShiftSiteContrast
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (packet : Finset E) (hpacket : packet.Nonempty) (z : E → ℂ) :
    spectralPacketResponse
        (L.productSpectralInteractionShiftSiteContrast onsite hinj
          x alternative sites) packet z =
      spectralPacketSiteContrast L onsite hinj
        x alternative sites packet z := by
  unfold productSpectralInteractionShiftSiteContrast
  unfold dependentHigherCoordinateContrast
  rw [show spectralPacketResponse
      (fun z =>
        finsetMobiusResponse sites
          (fun active =>
            L.productSpectralInteractionShift onsite hinj
              (dependentUpdateOnFinset x alternative active) z))
      packet z =
      finsetMobiusResponse packet
        (fun packetActive =>
          finsetMobiusResponse sites
            (fun siteActive =>
              L.productSpectralInteractionShift onsite hinj
                (dependentUpdateOnFinset x alternative siteActive)
                (restrictInteractionPacket packetActive z))) by rfl]
  rw [finsetMobiusResponse_comm]
  unfold productSpectralInteractionShift
  unfold spectralPacketSiteContrast dependentHigherCoordinateContrast
  apply congrArg (finsetMobiusResponse sites)
  funext siteActive
  exact spectralPacketResponse_sub_const_of_nonempty
    (L.productEigenvalueBranch onsite hinj
      (dependentUpdateOnFinset x alternative siteActive))
    (onsiteProductEnergy onsite
      (dependentUpdateOnFinset x alternative siteActive))
    packet hpacket z

/-- **Direct observer-sector zero criterion.**  The full observer contrast
vanishes as a germ exactly when every observer-spanning connected packet
sector vanishes as a germ. -/
theorem productSpectralInteractionShiftSiteContrast_germ_eq_zero_iff
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V) :
    L.productSpectralInteractionShiftSiteContrast onsite hinj
        x alternative sites =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) ↔
      ∀ packet, ObserverSpanningPacket L sites packet →
        spectralPacketSiteContrast L onsite hinj
          x alternative sites packet =ᶠ[𝓝 0]
            (fun _ : E → ℂ => 0) := by
  classical
  constructor
  · intro hzero packet hpacket
    have hp :=
      spectralPacketResponse_congr_germ hzero packet
    filter_upwards [hp] with z hz
    rw [← L.spectralPacketResponse_productSpectralInteractionShiftSiteContrast
      onsite hinj x alternative sites packet hpacket.1 z]
    simpa [spectralPacketResponse, finsetMobiusResponse] using hz
  · intro hpackets
    have hdecomp :=
      L.productSpectralInteractionShiftSiteContrast_eq_sum_observerSpanningPackets_germ
        onsite hinj x alternative sites
    have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
        ∀ packet ∈ observerSpanningPackets L sites,
          spectralPacketSiteContrast L onsite hinj
            x alternative sites packet z = 0 := by
      rw [Finset.eventually_all]
      intro packet hpacket
      exact hpackets packet (Finset.mem_filter.mp hpacket).2
    filter_upwards [hdecomp, hall] with z hz hpacketZero
    rw [hz]
    apply Finset.sum_eq_zero
    intro packet hpacket
    exact hpacketZero packet hpacket

/-- **Exact observer visibility criterion.**  The observer contrast is a
nonzero germ exactly when at least one spatially indecomposable interaction
packet spanning every queried site has nonzero irreducible response. -/
theorem productSpectralInteractionShiftSiteContrast_germ_ne_zero_iff
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V) :
    ¬L.productSpectralInteractionShiftSiteContrast onsite hinj
        x alternative sites =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) ↔
      ∃ packet, ObserverSpanningPacket L sites packet ∧
        ¬spectralPacketSiteContrast L onsite hinj
          x alternative sites packet =ᶠ[𝓝 0]
            (fun _ : E → ℂ => 0) := by
  constructor
  · intro hvisible
    by_contra hnoPacket
    push Not at hnoPacket
    exact hvisible
      ((L.productSpectralInteractionShiftSiteContrast_germ_eq_zero_iff
        onsite hinj x alternative sites).2 hnoPacket)
  · rintro ⟨packet, hpacket, hpacketVisible⟩ hzero
    exact hpacketVisible
      ((L.productSpectralInteractionShiftSiteContrast_germ_eq_zero_iff
        onsite hinj x alternative sites).1 hzero packet hpacket)

/-- An observer's spectral-time layer `n` is active when some nonzero
irreducible connected packet spanning the observer uses exactly `n`
interaction labels. -/
def ObserverSpectralTimeLayerActive
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (n : ℕ) : Prop :=
  ∃ packet, ObserverSpanningPacket L sites packet ∧
    packet.card = n ∧
    ¬spectralPacketSiteContrast L onsite hinj
      x alternative sites packet =ᶠ[𝓝 0]
        (fun _ : E → ℂ => 0)

/-- Observer visibility is equivalent to existence of an active finite
spectral-time layer. -/
theorem productSpectralInteractionShiftSiteContrast_germ_ne_zero_iff_exists_activeLayer
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V) :
    ¬L.productSpectralInteractionShiftSiteContrast onsite hinj
        x alternative sites =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) ↔
      ∃ n, ObserverSpectralTimeLayerActive L onsite hinj
        x alternative sites n := by
  rw [L.productSpectralInteractionShiftSiteContrast_germ_ne_zero_iff
    onsite hinj x alternative sites]
  constructor
  · rintro ⟨packet, hpacket, hnonzero⟩
    exact ⟨packet.card, packet, hpacket, rfl, hnonzero⟩
  · rintro ⟨n, packet, hpacket, hcard, hnonzero⟩
    exact ⟨packet, hpacket, hnonzero⟩

/-- Smallest number of jointly indispensable interaction labels carrying a
nonzero response for a visible observer contrast. -/
noncomputable def observerSpectralTimeDimension
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hvisible :
      ¬L.productSpectralInteractionShiftSiteContrast onsite hinj
          x alternative sites =ᶠ[𝓝 0] (fun _ : E → ℂ => 0)) : ℕ :=
  by
    classical
    exact Nat.find
      ((L.productSpectralInteractionShiftSiteContrast_germ_ne_zero_iff_exists_activeLayer
        onsite hinj x alternative sites).mp hvisible)

/-- The observer spectral-time dimension is itself an active layer. -/
theorem observerSpectralTimeDimension_active
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hvisible :
      ¬L.productSpectralInteractionShiftSiteContrast onsite hinj
          x alternative sites =ᶠ[𝓝 0] (fun _ : E → ℂ => 0)) :
    ObserverSpectralTimeLayerActive L onsite hinj x alternative sites
      (L.observerSpectralTimeDimension onsite hinj
        x alternative sites hvisible) :=
  by
    classical
    exact Nat.find_spec
      ((L.productSpectralInteractionShiftSiteContrast_germ_ne_zero_iff_exists_activeLayer
        onsite hinj x alternative sites).mp hvisible)

/-- The observer spectral-time dimension is no larger than any other active
layer. -/
theorem observerSpectralTimeDimension_le_of_active
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hvisible :
      ¬L.productSpectralInteractionShiftSiteContrast onsite hinj
          x alternative sites =ᶠ[𝓝 0] (fun _ : E → ℂ => 0))
    {n : ℕ}
    (hactive :
      ObserverSpectralTimeLayerActive L onsite hinj
        x alternative sites n) :
    L.observerSpectralTimeDimension onsite hinj
        x alternative sites hvisible ≤ n :=
  by
    classical
    exact Nat.find_min'
      ((L.productSpectralInteractionShiftSiteContrast_germ_ne_zero_iff_exists_activeLayer
        onsite hinj x alternative sites).mp hvisible)
      hactive

/-- Every purely geometric observer-Steiner lower bound also bounds the
actual observer spectral-time dimension. -/
theorem observerSteinerLowerBound_le_observerSpectralTimeDimension
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hvisible :
      ¬L.productSpectralInteractionShiftSiteContrast onsite hinj
          x alternative sites =ᶠ[𝓝 0] (fun _ : E → ℂ => 0))
    (r : ℕ) (hr : ObserverSteinerLowerBound L sites r) :
    r ≤ L.observerSpectralTimeDimension onsite hinj
      x alternative sites hvisible := by
  obtain ⟨packet, hpacket, hcard, hnonzero⟩ :=
    L.observerSpectralTimeDimension_active onsite hinj
      x alternative sites hvisible
  rw [← hcard]
  exact hr packet hpacket

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
