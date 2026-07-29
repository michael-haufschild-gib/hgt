import GaloisForLFunctions.HTGeometry.LocalSpectralPacketResponseLocality

/-!
# Observer hypergraph-Steiner law for local spectral branches

This file combines two Boolean Möbius decompositions.  The first decomposes an
analytic eigenvalue branch by interaction packets.  The second asks which
product-state sites can be distinguished by an observer contrast.

Only spatially indecomposable interaction packets spanning every queried site
survive both probes.  A packet of cardinality `n` contributes only at order
`O (‖g‖ ^ n)` along every scalar coupling ray.  Consequently the smallest
connected spanning packet gives an unconditional lower bound on observable
spectral onset.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- Site contrast of the irreducible spectral response carried by one
interaction packet. -/
noncomputable def spectralPacketSiteContrast
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (packet : Finset E) (z : E → ℂ) : ℂ :=
  dependentHigherCoordinateContrast x alternative sites
    (fun config => spectralPacketResponse
      (L.productEigenvalueBranch onsite hinj config) packet z)

/-- A nonempty packet that misses one queried site has zero site contrast. -/
theorem spectralPacketSiteContrast_germ_eq_zero_of_miss
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (packet : Finset E) (hpacket : packet.Nonempty)
    {i : V} (hi_sites : i ∈ sites)
    (hi_support : i ∉ L.packetSiteSupport packet) :
    spectralPacketSiteContrast L onsite hinj x alternative sites packet
      =ᶠ[𝓝 0] (fun _ : E → ℂ => (0 : ℂ)) := by
  have hactive : ∀ active : Finset V,
      spectralPacketResponse
        (L.productEigenvalueBranch onsite hinj
          (dependentUpdateOnFinset x alternative (insert i active))) packet
        =ᶠ[𝓝 0]
      spectralPacketResponse
        (L.productEigenvalueBranch onsite hinj
          (dependentUpdateOnFinset x alternative active)) packet := by
    intro active
    apply L.productEigenvalueBranch_spectralPacketResponse_germ_eq_of_eqOn
      onsite hinj packet hpacket
    intro v hv
    have hvi : v ≠ i := by
      intro h
      exact hi_support (h ▸ hv)
    simp [dependentUpdateOnFinset, hvi]
  have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
      ∀ active ∈ (Finset.univ : Finset (Finset V)),
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj
            (dependentUpdateOnFinset x alternative (insert i active))) packet z =
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj
            (dependentUpdateOnFinset x alternative active)) packet z := by
    rw [Finset.eventually_all]
    intro active hactiveMem
    exact hactive active
  filter_upwards [hall] with z hz
  unfold spectralPacketSiteContrast dependentHigherCoordinateContrast
  apply finsetMobiusResponse_eq_zero_of_insert_invariant hi_sites
  intro active
  exact hz active (Finset.mem_univ _)

omit [∀ v, Nonempty (A v)] in
/-- A packet of `n` interactions contributes only at order `O (‖g‖ ^ n)`
along every scalar coupling ray. -/
theorem spectralPacketSiteContrast_couplingRay_isBigO
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (packet : Finset E) (z : E → ℂ) :
    (fun g : ℂ => spectralPacketSiteContrast L onsite hinj
      x alternative sites packet (g • z))
      =O[𝓝 0] fun g : ℂ => ‖g‖ ^ packet.card := by
  unfold spectralPacketSiteContrast dependentHigherCoordinateContrast
  unfold finsetMobiusResponse
  apply IsBigO.sum
  intro d hd
  let config := dependentUpdateOnFinset x alternative (sites \ d)
  have hb := spectralPacketResponse_couplingRay_isBigO
    (L.productEigenvalueBranch onsite hinj config)
    (L.productEigenvalueBranch_spec onsite hinj config).1 z packet
  exact hb.const_mul_left ((-1 : ℂ) ^ d.card)

end FiniteLocalInteractionFamily

/-- A dependent site contrast distributes over a finite sum. -/
lemma dependentHigherCoordinateContrast_sum
    {V I R : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq I] [CommRing R]
    {A : V → Type*}
    (x alternative : ∀ v, A v) (sites : Finset V)
    (indices : Finset I) (f : I → (∀ v, A v) → R) :
    dependentHigherCoordinateContrast x alternative sites
      (∑ i ∈ indices, f i) =
    ∑ i ∈ indices,
      dependentHigherCoordinateContrast x alternative sites (f i) := by
  unfold dependentHigherCoordinateContrast
  change finsetMobiusResponseLinear sites
    (fun active => (∑ i ∈ indices, f i)
      (dependentUpdateOnFinset x alternative active)) = _
  have hfun :
      (fun active => (∑ i ∈ indices, f i)
        (dependentUpdateOnFinset x alternative active)) =
      ∑ i ∈ indices, (fun active =>
        f i (dependentUpdateOnFinset x alternative active)) := by
    funext active
    simp
  rw [hfun, map_sum]
  simp

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- Interaction-induced displacement of a simple product eigenvalue branch. -/
noncomputable def productSpectralInteractionShift
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (config : ∀ v, A v) (z : E → ℂ) : ℂ :=
  L.productEigenvalueBranch onsite hinj config z -
    onsiteProductEnergy onsite config

/-- Observer site contrast of the interaction-induced spectral displacement. -/
noncomputable def productSpectralInteractionShiftSiteContrast
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ) : ℂ :=
  dependentHigherCoordinateContrast x alternative sites
    (fun config => L.productSpectralInteractionShift onsite hinj config z)

omit [Fintype E] in
lemma spectralPacketResponse_empty
    (branch : (E → ℂ) → ℂ) (z : E → ℂ) :
    spectralPacketResponse branch ∅ z = branch 0 := by
  have hzero : restrictInteractionPacket ∅ z = (0 : E → ℂ) := by
    funext e
    simp [restrictInteractionPacket]
  simp [spectralPacketResponse, finsetMobiusResponse, hzero]

omit [∀ v, Nonempty (A v)] in
/-- The interaction-induced shift is exactly the sum of all nonempty packet
responses. -/
lemma productSpectralInteractionShift_eq_sum_nonemptyPackets
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (config : ∀ v, A v) (z : E → ℂ) :
    L.productSpectralInteractionShift onsite hinj config z =
      ∑ packet ∈ (Finset.univ : Finset (Finset E)).erase ∅,
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj config) packet z := by
  let branch := L.productEigenvalueBranch onsite hinj config
  have h0 : branch 0 = onsiteProductEnergy onsite config :=
    (L.productEigenvalueBranch_spec onsite hinj config).2.1
  have hall := sum_spectralPacketResponse_eq_branch branch z
  have hempty := spectralPacketResponse_empty branch z
  unfold productSpectralInteractionShift
  change branch z - onsiteProductEnergy onsite config = _
  rw [← h0, ← hempty, ← hall]
  rw [← Finset.sum_erase_add
    (Finset.univ : Finset (Finset E))
    (fun packet => spectralPacketResponse branch packet z)
    (Finset.mem_univ (∅ : Finset E))]
  abel

omit [∀ v, Nonempty (A v)] in
/-- The observer contrast is exactly the sum of all nonempty packet
contrasts. -/
theorem productSpectralInteractionShiftSiteContrast_eq_sum_nonemptyPackets
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ) :
    L.productSpectralInteractionShiftSiteContrast onsite hinj
      x alternative sites z =
      ∑ packet ∈ (Finset.univ : Finset (Finset E)).erase ∅,
        spectralPacketSiteContrast L onsite hinj x alternative sites packet z := by
  unfold productSpectralInteractionShiftSiteContrast
  rw [show (fun config => L.productSpectralInteractionShift onsite hinj config z) =
      ∑ packet ∈ (Finset.univ : Finset (Finset E)).erase ∅,
        (fun config => spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj config) packet z) by
    funext config
    simpa only [Finset.sum_apply] using
      L.productSpectralInteractionShift_eq_sum_nonemptyPackets
        onsite hinj config z]
  rw [dependentHigherCoordinateContrast_sum]
  rfl

/-- Spatially disconnected packets have zero observer contrast. -/
theorem spectralPacketSiteContrast_germ_eq_zero_of_disconnected
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (packet : Finset E) (hpacket : SpatiallyDisconnectedPacket L packet) :
    spectralPacketSiteContrast L onsite hinj x alternative sites packet
      =ᶠ[𝓝 0] (fun _ : E → ℂ => (0 : ℂ)) := by
  have hactive : ∀ active : Finset V,
      spectralPacketResponse
        (L.productEigenvalueBranch onsite hinj
          (dependentUpdateOnFinset x alternative active)) packet
        =ᶠ[𝓝 0] (fun _ : E → ℂ => (0 : ℂ)) := by
    intro active
    let config := dependentUpdateOnFinset x alternative active
    have hs := L.productEigenvalueBranch_spec onsite hinj config
    exact L.globalBranch_spectralPacketResponse_germ_eq_zero_of_disconnected
      onsite hinj config (L.productEigenvalueBranch onsite hinj config)
      hs.1 hs.2.1 hs.2.2 packet hpacket
  have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
      ∀ active ∈ Finset.Iic sites,
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj
            (dependentUpdateOnFinset x alternative active)) packet z = 0 := by
    rw [Finset.eventually_all]
    intro active hactiveMem
    exact hactive active
  filter_upwards [hall] with z hz
  unfold spectralPacketSiteContrast dependentHigherCoordinateContrast
  unfold finsetMobiusResponse
  apply Finset.sum_eq_zero
  intro d hd
  change (-1 : ℂ) ^ d.card *
    spectralPacketResponse
      (L.productEigenvalueBranch onsite hinj
        (dependentUpdateOnFinset x alternative (sites \ d)))
      packet z = 0
  rw [hz (sites \ d)
    (Finset.mem_Iic.mpr Finset.sdiff_subset)]
  simp

/-- A packet is observable on `sites` exactly when it is nonempty, spatially
indecomposable, and touches every queried site. -/
def ObserverSpanningPacket
    (L : FiniteLocalInteractionFamily V E A)
    (sites : Finset V) (packet : Finset E) : Prop :=
  packet.Nonempty ∧ ¬SpatiallyDisconnectedPacket L packet ∧
    sites ⊆ L.packetSiteSupport packet

/-- Finite collection of all observer-spanning packets. -/
noncomputable def observerSpanningPackets
    (L : FiniteLocalInteractionFamily V E A)
    (sites : Finset V) : Finset (Finset E) := by
  classical
  exact (Finset.univ : Finset (Finset E)).filter
    (ObserverSpanningPacket L sites)

/-- **Exact connected-packet observer decomposition.**  As a germ at zero
coupling, the full observer contrast is exactly the sum over nonempty,
spatially indecomposable packets spanning every observed site. -/
theorem productSpectralInteractionShiftSiteContrast_eq_sum_observerSpanningPackets_germ
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V) :
    L.productSpectralInteractionShiftSiteContrast onsite hinj
      x alternative sites =ᶠ[𝓝 0]
    (fun z => ∑ packet ∈ observerSpanningPackets L sites,
      spectralPacketSiteContrast L onsite hinj x alternative sites packet z) := by
  classical
  let nonemptyPackets := (Finset.univ : Finset (Finset E)).erase ∅
  let excludedPackets := nonemptyPackets \ observerSpanningPackets L sites
  have hzero : ∀ packet ∈ excludedPackets,
      spectralPacketSiteContrast L onsite hinj x alternative sites packet
        =ᶠ[𝓝 0] (fun _ : E → ℂ => (0 : ℂ)) := by
    intro packet hpacket
    have hpnonempty : packet.Nonempty := by
      have hmemNon := (Finset.mem_sdiff.mp hpacket).1
      have hne : packet ≠ ∅ := by
        simpa [nonemptyPackets] using hmemNon
      exact Finset.nonempty_iff_ne_empty.mpr hne
    have hpnot : ¬ObserverSpanningPacket L sites packet := by
      intro hp
      exact (Finset.mem_sdiff.mp hpacket).2
        (by simp [observerSpanningPackets, hp])
    by_cases hdisc : SpatiallyDisconnectedPacket L packet
    · exact spectralPacketSiteContrast_germ_eq_zero_of_disconnected
        L onsite hinj x alternative sites packet hdisc
    · have hnsubset : ¬sites ⊆ L.packetSiteSupport packet := by
        intro hsub
        exact hpnot ⟨hpnonempty, hdisc, hsub⟩
      obtain ⟨i, hi_sites, hi_support⟩ := Finset.not_subset.mp hnsubset
      exact spectralPacketSiteContrast_germ_eq_zero_of_miss
        L onsite hinj x alternative sites packet hpnonempty
        hi_sites hi_support
  have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
      ∀ packet ∈ excludedPackets,
        spectralPacketSiteContrast L onsite hinj x alternative sites packet z = 0 := by
    rw [Finset.eventually_all]
    intro packet hpacket
    exact hzero packet hpacket
  filter_upwards [hall] with z hz
  rw [productSpectralInteractionShiftSiteContrast_eq_sum_nonemptyPackets]
  symm
  apply Finset.sum_subset
  · intro packet hpacket
    have hp := (Finset.mem_filter.mp hpacket).2.1
    exact Finset.mem_erase.mpr ⟨Finset.Nonempty.ne_empty hp, Finset.mem_univ _⟩
  · intro packet hpacket hnot
    exact hz packet (Finset.mem_sdiff.mpr ⟨hpacket, hnot⟩)

/-- Higher powers vanish at least as fast as lower powers near zero. -/
lemma norm_pow_isBigO_norm_pow_of_le (r n : ℕ) (h : r ≤ n) :
    (fun g : ℂ => ‖g‖ ^ n) =O[𝓝 0]
      (fun g : ℂ => ‖g‖ ^ r) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with g hg
  have hg1 : ‖g‖ ≤ 1 := by
    have hlt : ‖g‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hg
    exact hlt.le
  simp only [norm_pow, Real.norm_eq_abs, abs_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg g) hg1 h

/-- `r` is a lower bound for the number of interactions in every spatially
indecomposable packet spanning all observed sites. -/
def ObserverSteinerLowerBound
    (L : FiniteLocalInteractionFamily V E A)
    (sites : Finset V) (r : ℕ) : Prop :=
  ∀ packet, ObserverSpanningPacket L sites packet → r ≤ packet.card

/-- **Observer hypergraph-Steiner onset law.**  Along every scalar interaction
ray, an observer contrast cannot appear below the size of the smallest
spatially indecomposable interaction packet spanning all queried sites. -/
theorem productSpectralInteractionShiftSiteContrast_couplingRay_isBigO
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (r : ℕ) (hr : ObserverSteinerLowerBound L sites r)
    (z : E → ℂ) :
    (fun g : ℂ =>
      L.productSpectralInteractionShiftSiteContrast onsite hinj
        x alternative sites (g • z))
      =O[𝓝 0] fun g : ℂ => ‖g‖ ^ r := by
  classical
  let ray : ℂ → (E → ℂ) := fun g => g • z
  have hray : Tendsto ray (𝓝 0) (𝓝 0) := by
    have hc : Continuous ray := continuous_id.smul continuous_const
    have hc0 : ContinuousAt ray 0 := hc.continuousAt
    change Tendsto ray (𝓝 0) (𝓝 (ray 0)) at hc0
    simpa only [ray, zero_smul] using hc0
  have hdecomp :=
    L.productSpectralInteractionShiftSiteContrast_eq_sum_observerSpanningPackets_germ
      onsite hinj x alternative sites
  have hpull := hdecomp.comp_tendsto hray
  have hsum :
      (fun g : ℂ =>
        ∑ packet ∈ observerSpanningPackets L sites,
          spectralPacketSiteContrast L onsite hinj
            x alternative sites packet (g • z))
        =O[𝓝 0] fun g : ℂ => ‖g‖ ^ r := by
    apply IsBigO.sum
    intro packet hpacket
    have hp : ObserverSpanningPacket L sites packet :=
      (Finset.mem_filter.mp hpacket).2
    exact
      (spectralPacketSiteContrast_couplingRay_isBigO
        L onsite hinj x alternative sites packet z).trans
      (norm_pow_isBigO_norm_pow_of_le r packet.card (hr packet hp))
  exact hsum.congr' hpull.symm Filter.EventuallyEq.rfl

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
