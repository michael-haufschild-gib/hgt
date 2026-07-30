import GaloisForLFunctions.HTGeometry.LocalSpectralObserverDirectSumLaw

/-!
# Weighted Newton law for interaction packets

An independently switchable interaction label may be assigned any positive
integer switch-on weight.  Replacing that coordinate by a product of as many
virtual coordinates as its weight converts weighted onset into ordinary
Boolean packet depth.  Consequently an analytic response requiring every
label in a packet is delayed by at least the sum of the label weights.

This is the multiscale refinement of the scalar packet-depth law: ordinary
packet cardinality is the special case in which every interaction has weight
one.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Virtual labels obtained by replacing interaction `e` with `weight e`
independently switchable replicas. -/
abbrev ReplicatedInteractionLabel
    (packet : Finset E) (weight : E → ℕ) :=
  Σ e : packet, Fin (weight e.1)

/-- Collapse replicated coordinates by multiplying all replicas belonging to
the same original interaction label. -/
def replicatedProductCoupling
    (packet : Finset E) (weight : E → ℕ)
    (y : ReplicatedInteractionLabel packet weight → ℂ) : E → ℂ :=
  fun e =>
    if he : e ∈ packet then
      ∏ j : Fin (weight e), y ⟨⟨e, he⟩, j⟩
    else 0

/-- The replicated-product collapse is analytic at the decoupled point. -/
theorem analyticAt_replicatedProductCoupling
    (packet : Finset E) (weight : E → ℕ) :
    AnalyticAt ℂ (replicatedProductCoupling packet weight) 0 := by
  unfold replicatedProductCoupling
  apply AnalyticAt.pi
  intro e
  split
  · apply Finset.analyticAt_fun_prod
    intro j hj
    exact
      ((ContinuousLinearMap.proj
        (R := ℂ) (⟨⟨e, ‹e ∈ packet›⟩, j⟩ :
          ReplicatedInteractionLabel packet weight) :
          (ReplicatedInteractionLabel packet weight → ℂ) →L[ℂ] ℂ).analyticAt 0)
  · exact analyticAt_const

/-- Positive weights make the replicated origin collapse to the original
decoupled point. -/
theorem replicatedProductCoupling_zero
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e ∈ packet, 0 < weight e) :
    replicatedProductCoupling packet weight 0 = 0 := by
  funext e
  by_cases he : e ∈ packet
  · simp [replicatedProductCoupling, he, Nat.ne_of_gt (hpos e he)]
  · simp [replicatedProductCoupling, he]

/-- Direction amplitude left after extracting the weighted scalar power. -/
def replicatedInteractionAmplitude
    (packet : Finset E) (weight : E → ℕ)
    (direction : ReplicatedInteractionLabel packet weight → ℂ) : E → ℂ :=
  fun e =>
    if he : e ∈ packet then
      ∏ j : Fin (weight e), direction ⟨⟨e, he⟩, j⟩
    else 0

/-- Canonical factorization of an arbitrary original packet direction:
place its amplitude in the first replica and put one in every other
replica. -/
noncomputable def canonicalReplicatedInteractionDirection
    (packet : Finset E) (weight : E → ℕ)
    (z : E → ℂ) :
    ReplicatedInteractionLabel packet weight → ℂ :=
  fun label =>
    if label.2.val = 0 then z label.1.1 else 1

/-- Canonical replication recovers the original direction on the packet. -/
theorem replicatedInteractionAmplitude_canonical
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e ∈ packet, 0 < weight e)
    (z : E → ℂ) :
    replicatedInteractionAmplitude packet weight
        (canonicalReplicatedInteractionDirection packet weight z) =
      restrictInteractionPacket packet z := by
  funext e
  by_cases he : e ∈ packet
  · simp only [replicatedInteractionAmplitude, he, dite_true,
      restrictInteractionPacket, if_pos]
    let first : Fin (weight e) := ⟨0, hpos e he⟩
    rw [Finset.prod_eq_single first
      (fun j _ hj => by
        have hjval : j.val ≠ 0 := by
          intro hzero
          apply hj
          apply Fin.ext
          simpa [first] using hzero
        simp [canonicalReplicatedInteractionDirection, hjval])
      (fun h => absurd (Finset.mem_univ first) h)]
    simp [canonicalReplicatedInteractionDirection, first]
  · simp [replicatedInteractionAmplitude,
      restrictInteractionPacket, he]

/-- A scalar ray in replica space becomes the weighted monomial switch-on
`g ↦ g^(weight e)` in the original coupling space. -/
theorem replicatedProductCoupling_smul
    (packet : Finset E) (weight : E → ℕ)
    (direction : ReplicatedInteractionLabel packet weight → ℂ) (g : ℂ) :
    replicatedProductCoupling packet weight (g • direction) =
      fun e =>
        g ^ weight e *
          replicatedInteractionAmplitude packet weight direction e := by
  funext e
  by_cases he : e ∈ packet
  · simp only [replicatedProductCoupling, replicatedInteractionAmplitude,
      he, dite_true, Pi.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    simp
  · simp [replicatedProductCoupling, replicatedInteractionAmplitude, he]

/-- Omitting one virtual label forces at least one required original
interaction coordinate to zero. -/
theorem replicatedProductCoupling_eq_zero_of_missing
    (packet : Finset E) (weight : E → ℕ)
    (active : Finset (ReplicatedInteractionLabel packet weight))
    (direction : ReplicatedInteractionLabel packet weight → ℂ)
    (hactive : active ≠ Finset.univ) :
    ∃ e ∈ packet,
      replicatedProductCoupling packet weight
          (restrictInteractionPacket active direction) e = 0 := by
  have hnot :
      ¬(Finset.univ :
        Finset (ReplicatedInteractionLabel packet weight)) ⊆ active := by
    simpa using hactive
  obtain ⟨label, hlabelUniv, hlabelActive⟩ :=
    Finset.not_subset.mp hnot
  refine ⟨label.1.1, label.1.2, ?_⟩
  simp only [replicatedProductCoupling, label.1.2, dite_true]
  apply Finset.prod_eq_zero (Finset.mem_univ label.2)
  simp [restrictInteractionPacket, hlabelActive]

/-- A packet response composed with replicated products vanishes after any
proper replica restriction. -/
theorem spectralPacketResponse_replicatedProductCoupling_eq_zero_of_missing
    (branch : (E → ℂ) → ℂ)
    (packet : Finset E) (weight : E → ℕ)
    (active : Finset (ReplicatedInteractionLabel packet weight))
    (direction : ReplicatedInteractionLabel packet weight → ℂ)
    (hactive : active ≠ Finset.univ) :
    spectralPacketResponse branch packet
        (replicatedProductCoupling packet weight
          (restrictInteractionPacket active direction)) = 0 := by
  obtain ⟨e, hepacket, hezero⟩ :=
    replicatedProductCoupling_eq_zero_of_missing
      packet weight active direction hactive
  let originalActive := packet.erase e
  have hcoupling :
      replicatedProductCoupling packet weight
          (restrictInteractionPacket active direction) =
        restrictInteractionPacket originalActive
          (replicatedProductCoupling packet weight
            (restrictInteractionPacket active direction)) := by
    funext i
    by_cases hi : i = e
    · subst i
      simp [restrictInteractionPacket, originalActive, hezero]
    · by_cases hipacket : i ∈ packet
      · simp [restrictInteractionPacket, originalActive, hi, hipacket]
      · simp [replicatedProductCoupling, restrictInteractionPacket,
          originalActive, hi, hipacket]
  rw [hcoupling, spectralPacketResponse_restrictInteractionPacket]
  rw [if_neg]
  intro hsub
  have he := hsub hepacket
  simpa [originalActive] using he

/-- The replica-space full packet projector returns the original packet
response after product collapse. -/
theorem spectralPacketResponse_full_replicated_eq
    (branch : (E → ℂ) → ℂ)
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e ∈ packet, 0 < weight e)
    (direction : ReplicatedInteractionLabel packet weight → ℂ) :
    spectralPacketResponse
        (fun y => spectralPacketResponse branch packet
          (replicatedProductCoupling packet weight y))
        Finset.univ direction =
      spectralPacketResponse branch packet
        (replicatedProductCoupling packet weight direction) := by
  change finsetMobiusResponse Finset.univ
      (fun active =>
        spectralPacketResponse branch packet
          (replicatedProductCoupling packet weight
            (restrictInteractionPacket active direction))) =
    spectralPacketResponse branch packet
      (replicatedProductCoupling packet weight direction)
  unfold finsetMobiusResponse
  rw [Finset.sum_eq_single ∅]
  · have huniv :
        restrictInteractionPacket
            (Finset.univ :
              Finset (ReplicatedInteractionLabel packet weight))
            direction =
          direction := by
        funext label
        simp [restrictInteractionPacket]
    simp only [Finset.card_empty, pow_zero, one_mul,
      Finset.sdiff_empty]
    rw [huniv]
  · intro d hd hne
    have hproper :
        (Finset.univ \ d :
          Finset (ReplicatedInteractionLabel packet weight)) ≠
            Finset.univ := by
      intro h
      have : d = ∅ := by
        ext label
        have hm := congrArg (fun s => label ∈ s) h
        simpa using hm
      exact hne this
    change (-1 : ℂ) ^ d.card *
      spectralPacketResponse branch packet
        (replicatedProductCoupling packet weight
          (restrictInteractionPacket (Finset.univ \ d) direction)) = 0
    rw [
      spectralPacketResponse_replicatedProductCoupling_eq_zero_of_missing
        branch packet weight (Finset.univ \ d) direction hproper]
    simp
  · simp

/-- **Weighted packet-depth law.** Along every positive integer-weighted
monomial switch-on, an analytic irreducible packet response is delayed by
at least the total packet weight. -/
theorem spectralPacketResponse_weightedCouplingRay_isBigO
    (branch : (E → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e ∈ packet, 0 < weight e)
    (direction : ReplicatedInteractionLabel packet weight → ℂ) :
    (fun g : ℂ =>
      spectralPacketResponse branch packet
        (fun e =>
          g ^ weight e *
            replicatedInteractionAmplitude packet weight direction e))
      =O[𝓝 0]
    fun g : ℂ => ‖g‖ ^ ∑ e ∈ packet, weight e := by
  let lifted :
      (ReplicatedInteractionLabel packet weight → ℂ) → ℂ :=
    fun y =>
      spectralPacketResponse branch packet
        (replicatedProductCoupling packet weight y)
  have hlifted : AnalyticAt ℂ lifted 0 := by
    have hproduct :=
      analyticAt_replicatedProductCoupling packet weight
    have hproduct0 :=
      replicatedProductCoupling_zero packet weight hpos
    dsimp [lifted]
    unfold spectralPacketResponse finsetMobiusResponse
    apply Finset.analyticAt_fun_sum
    intro d hd
    have hrestrict :=
      restrictInteractionPacket_analyticAt (packet \ d)
    have hrestrictedProduct :
        AnalyticAt ℂ
          (fun y =>
            restrictInteractionPacket (packet \ d)
              (replicatedProductCoupling packet weight y)) 0 := by
      have hrestrictAtProduct :
          AnalyticAt ℂ
            (fun coupling : E → ℂ =>
              restrictInteractionPacket (packet \ d) coupling)
            (replicatedProductCoupling packet weight 0) := by
        simpa [hproduct0] using hrestrict
      simpa [Function.comp_def] using
        hrestrictAtProduct.comp hproduct
    have hbranchComp :
        AnalyticAt ℂ
          (fun y =>
            branch
              (restrictInteractionPacket (packet \ d)
                (replicatedProductCoupling packet weight y))) 0 := by
      have hrestricted0 :
          restrictInteractionPacket (packet \ d)
              (replicatedProductCoupling packet weight 0) = 0 := by
        rw [hproduct0]
        funext e
        simp [restrictInteractionPacket]
      simpa [Function.comp_def] using
        hbranch.comp_of_eq hrestrictedProduct hrestricted0
    convert
      hbranchComp.const_smul (c := (-1 : ℂ) ^ d.card) using 1
    funext y
    simp [smul_eq_mul]
  have hdepth :=
    spectralPacketResponse_couplingRay_isBigO
      lifted hlifted direction
        (Finset.univ :
          Finset (ReplicatedInteractionLabel packet weight))
  have hcard :
      (Finset.univ :
        Finset (ReplicatedInteractionLabel packet weight)).card =
      ∑ e ∈ packet, weight e := by
    simpa [ReplicatedInteractionLabel] using
      (Finset.sum_attach packet weight)
  rw [hcard] at hdepth
  apply hdepth.congr_left
  intro g
  rw [spectralPacketResponse_full_replicated_eq
    branch packet weight hpos]
  rw [replicatedProductCoupling_smul]

/-- Arbitrary-direction form of the weighted packet-depth law. -/
theorem spectralPacketResponse_weightedMonomialRay_isBigO
    (branch : (E → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e ∈ packet, 0 < weight e)
    (z : E → ℂ) :
    (fun g : ℂ =>
      spectralPacketResponse branch packet
        (fun e => g ^ weight e *
          restrictInteractionPacket packet z e))
      =O[𝓝 0]
    fun g : ℂ => ‖g‖ ^ ∑ e ∈ packet, weight e := by
  have h :=
    spectralPacketResponse_weightedCouplingRay_isBigO
      branch hbranch packet weight hpos
        (canonicalReplicatedInteractionDirection packet weight z)
  simpa [replicatedInteractionAmplitude_canonical
    packet weight hpos z] using h

/-- Global-direction form: coordinates outside the queried packet are
irrelevant to that packet projector. -/
theorem spectralPacketResponse_globalWeightedMonomialRay_isBigO
    (branch : (E → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e ∈ packet, 0 < weight e)
    (z : E → ℂ) :
    (fun g : ℂ =>
      spectralPacketResponse branch packet
        (fun e => g ^ weight e * z e))
      =O[𝓝 0]
    fun g : ℂ => ‖g‖ ^ ∑ e ∈ packet, weight e := by
  have h :=
    spectralPacketResponse_weightedMonomialRay_isBigO
      branch hbranch packet weight hpos z
  apply h.congr_left
  intro g
  rw [show
      (fun e => g ^ weight e *
        restrictInteractionPacket packet z e) =
      restrictInteractionPacket packet
        (fun e => g ^ weight e * z e) by
      funext e
      by_cases he : e ∈ packet <;>
        simp [restrictInteractionPacket, he]]
  rw [spectralPacketResponse_restrictInteractionPacket]
  simp

end GaloisForLFunctions.HTGeometry
