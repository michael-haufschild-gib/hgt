import GaloisForLFunctions.RHTower.ThetaCuspHawkingArbitraryGlobalSchwarzOddPeierlsResponseRigidity

/-!
# Retarded/advanced reciprocity--Schwarz causal rigidity

On the global finite-support Xi carrier, one retarded/advanced pairing-reciprocity law and one
retarded-to-advanced Schwarz-exchange law force the retarded-minus-advanced jump to be
Peierls-skew and channel-Schwarz odd. Conversely every arbitrary global propagator with those two
properties has the canonical reciprocal, Schwarz-exchanged half-jump decomposition
`Gret = Delta / 2`, `Gadv = -Delta / 2`.

Thus minimal algebraic Green-pair structure is exactly equivalent to the monolithic causal laws of
the arbitrary-global obstruction. Universal literal unit BM incidence for such a pair exists if
and only if RH. No diagonal, local, support, boundedness, or fibre-preservation hypothesis is used.
The maps here are abstract response maps: PDE inverse and causal-support laws remain producer data.

`[NEW] [RETARDED/ADVANCED] [RECIPROCITY] [SCHWARZ EXCHANGE] [CLASSIFICATION] [RH EQUIVALENCE] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- The global Xi carrier pairing is symmetric. -/
theorem hbXiPeierlsPairing_comm (f g : HBXiPeierlsCarrier) :
    hbXiPeierlsPairing f g = hbXiPeierlsPairing g f := by
  simp only [hbXiPeierlsPairing_apply]
  rw [hbXiPeierlsDot_comm f.1 g.1, hbXiPeierlsDot_comm f.2 g.2]

/-- One oriented Green-reciprocity law: the retarded response in the first slot is adjoint to the
advanced response in the second slot. -/
def HBXiPeierlsRetardedAdvancedReciprocal
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) : Prop :=
  ∀ f g : HBXiPeierlsCarrier,
    hbXiPeierlsPairing (Gret f) g = hbXiPeierlsPairing f (Gadv g)

/-- One oriented causal Schwarz law: Schwarz transport exchanges retarded with advanced response. -/
def HBXiPeierlsRetardedToAdvancedSchwarzExchange
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) : Prop :=
  ∀ f : HBXiPeierlsCarrier,
    hbXiPeierlsCanonicalChannelSchwarz (Gret f) =
      Gadv (hbXiPeierlsCanonicalChannelSchwarz f)

/-- Causal response jump, with the retarded-minus-advanced sign convention. -/
def hbXiPeierlsRetardedAdvancedCausalJump
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) :
    HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier :=
  Gret - Gadv

@[simp]
theorem hbXiPeierlsRetardedAdvancedCausalJump_apply
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (f : HBXiPeierlsCarrier) :
    hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv f = Gret f - Gadv f := rfl

/-- Symmetry of the carrier pairing turns one retarded/advanced reciprocity identity into its
reverse orientation. -/
theorem hbXiPeierlsRetardedAdvanced_reverseReciprocity
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hreciprocal : HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv)
    (f g : HBXiPeierlsCarrier) :
    hbXiPeierlsPairing (Gadv f) g = hbXiPeierlsPairing f (Gret g) := by
  calc
    hbXiPeierlsPairing (Gadv f) g = hbXiPeierlsPairing g (Gadv f) :=
      hbXiPeierlsPairing_comm _ _
    _ = hbXiPeierlsPairing (Gret g) f := (hreciprocal g f).symm
    _ = hbXiPeierlsPairing f (Gret g) := hbXiPeierlsPairing_comm _ _

/-- Involutivity of channel Schwarz transport turns the retarded-to-advanced exchange into the
advanced-to-retarded exchange. -/
theorem hbXiPeierlsRetardedAdvanced_reverseSchwarzExchange
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hexchange : HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv)
    (f : HBXiPeierlsCarrier) :
    hbXiPeierlsCanonicalChannelSchwarz (Gadv f) =
      Gret (hbXiPeierlsCanonicalChannelSchwarz f) := by
  have h := congrArg hbXiPeierlsCanonicalChannelSchwarz
    (hexchange (hbXiPeierlsCanonicalChannelSchwarz f))
  simp only [hbXiPeierlsCanonicalChannelSchwarz_involutive] at h
  exact h.symm

/-- Retarded/advanced reciprocity forces the causal jump to be Peierls-skew. -/
theorem hbXiPeierlsRetardedAdvancedCausalJump_skew
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hreciprocal : HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv) :
    HBXiPeierlsGlobalPropagatorSkew
      (hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv) := by
  intro f g
  change hbXiPeierlsPairing (Gret f - Gadv f) g =
    -hbXiPeierlsPairing (Gret g - Gadv g) f
  simp only [map_sub, LinearMap.sub_apply]
  rw [hreciprocal f g,
    hbXiPeierlsRetardedAdvanced_reverseReciprocity Gret Gadv hreciprocal f g,
    hbXiPeierlsPairing_comm f (Gadv g), hbXiPeierlsPairing_comm f (Gret g)]
  ring

/-- Schwarz exchange of the causal orientations forces their jump to be channel-Schwarz odd. -/
theorem hbXiPeierlsRetardedAdvancedCausalJump_channelSchwarzOdd
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hexchange : HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv) :
    HBXiPeierlsGlobalPropagatorChannelSchwarzOdd
      (hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv) := by
  intro f
  change hbXiPeierlsCanonicalChannelSchwarz (Gret f - Gadv f) =
    -(Gret (hbXiPeierlsCanonicalChannelSchwarz f) -
      Gadv (hbXiPeierlsCanonicalChannelSchwarz f))
  rw [map_sub, hexchange f,
    hbXiPeierlsRetardedAdvanced_reverseSchwarzExchange Gret Gadv hexchange f]
  abel

/-- Peierls skewness makes the positive and negative half-jumps reciprocal. -/
theorem hbXiPeierlsHalfJump_reciprocal
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hskew : HBXiPeierlsGlobalPropagatorSkew Delta) :
    HBXiPeierlsRetardedAdvancedReciprocal
      ((1 / 2 : ℂ) • Delta) (-((1 / 2 : ℂ) • Delta)) := by
  intro f g
  change hbXiPeierlsPairing ((1 / 2 : ℂ) • Delta f) g =
    hbXiPeierlsPairing f (-((1 / 2 : ℂ) • Delta g))
  simp only [map_smul, LinearMap.smul_apply, map_neg]
  rw [hbXiPeierlsPairing_comm f (Delta g)]
  have h := hskew f g
  change hbXiPeierlsPairing (Delta f) g =
    -hbXiPeierlsPairing (Delta g) f at h
  rw [h]
  ring

/-- Channel-Schwarz oddness makes the positive and negative half-jumps Schwarz exchanged. -/
theorem hbXiPeierlsHalfJump_retardedToAdvancedSchwarzExchange
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hodd : HBXiPeierlsGlobalPropagatorChannelSchwarzOdd Delta) :
    HBXiPeierlsRetardedToAdvancedSchwarzExchange
      ((1 / 2 : ℂ) • Delta) (-((1 / 2 : ℂ) • Delta)) := by
  intro f
  change hbXiPeierlsCanonicalChannelSchwarz ((1 / 2 : ℂ) • Delta f) =
    -((1 / 2 : ℂ) • Delta (hbXiPeierlsCanonicalChannelSchwarz f))
  rw [map_smulₛₗ, hodd f]
  rw [map_div₀, map_one, map_ofNat (starRingEnd ℂ) 2]
  norm_num

/-- The causal jump of the canonical positive and negative half-jumps is the original propagator. -/
theorem hbXiPeierlsHalfJump_causalJump
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) :
    hbXiPeierlsRetardedAdvancedCausalJump
      ((1 / 2 : ℂ) • Delta) (-((1 / 2 : ℂ) • Delta)) = Delta := by
  apply LinearMap.ext
  intro f
  change (1 / 2 : ℂ) • Delta f - (-((1 / 2 : ℂ) • Delta f)) = Delta f
  rw [sub_neg_eq_add]
  calc
    (1 / 2 : ℂ) • Delta f + (1 / 2 : ℂ) • Delta f =
        ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • Delta f :=
      (add_smul (1 / 2 : ℂ) (1 / 2 : ℂ) (Delta f)).symm
    _ = Delta f := by norm_num

/-- Exact operator-class classification: an arbitrary global propagator is Peierls-skew and
channel-Schwarz odd exactly when it is the causal jump of a reciprocal, Schwarz-exchanged pair. -/
theorem exists_hbXiPeierlsRetardedAdvanced_reciprocal_schwarzExchange_causalJump_eq_iff
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) :
    (∃ Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier,
      HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv ∧
        HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv ∧
          hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv = Delta) ↔
      HBXiPeierlsGlobalPropagatorSkew Delta ∧
        HBXiPeierlsGlobalPropagatorChannelSchwarzOdd Delta := by
  constructor
  · rintro ⟨Gret, Gadv, hreciprocal, hexchange, rfl⟩
    exact ⟨hbXiPeierlsRetardedAdvancedCausalJump_skew Gret Gadv hreciprocal,
      hbXiPeierlsRetardedAdvancedCausalJump_channelSchwarzOdd Gret Gadv hexchange⟩
  · rintro ⟨hskew, hodd⟩
    exact ⟨(1 / 2 : ℂ) • Delta, -((1 / 2 : ℂ) • Delta),
      hbXiPeierlsHalfJump_reciprocal Delta hskew,
      hbXiPeierlsHalfJump_retardedToAdvancedSchwarzExchange Delta hodd,
      hbXiPeierlsHalfJump_causalJump Delta⟩

/-- Green-pair endpoint: arbitrary global reciprocal, Schwarz-exchanged retarded/advanced response
maps can have a causal jump with universal exact unit BM incidence exactly when RH holds. -/
theorem exists_hbXiPeierlsRetardedAdvanced_reciprocal_schwarzExchange_and_universalUnitSourceIncidence_iff_rh
    (n : ℕ) :
    (∃ Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier,
      HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv ∧
        HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv ∧
          HBXiPeierlsGlobalPropagatorUniversalUnitSourceIncidence n
            (hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨Gret, Gadv, hreciprocal, hexchange, hincidence⟩
    exact
      (exists_hbXiPeierlsGlobalPropagator_skew_channelSchwarzOdd_and_universalUnitSourceIncidence_iff_rh
        n).1
        ⟨hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv,
          hbXiPeierlsRetardedAdvancedCausalJump_skew Gret Gadv hreciprocal,
          hbXiPeierlsRetardedAdvancedCausalJump_channelSchwarzOdd Gret Gadv hexchange,
          hincidence⟩
  · intro hRH
    obtain ⟨Delta, hskew, hodd, hincidence⟩ :=
      (exists_hbXiPeierlsGlobalPropagator_skew_channelSchwarzOdd_and_universalUnitSourceIncidence_iff_rh
        n).2 hRH
    refine ⟨(1 / 2 : ℂ) • Delta, -((1 / 2 : ℂ) • Delta),
      hbXiPeierlsHalfJump_reciprocal Delta hskew,
      hbXiPeierlsHalfJump_retardedToAdvancedSchwarzExchange Delta hodd, ?_⟩
    rw [hbXiPeierlsHalfJump_causalJump]
    exact hincidence

end

end RHTower
