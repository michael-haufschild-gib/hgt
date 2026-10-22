import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTargetIndependentFullCokernelPeierlsRealization
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingRetardedAdvancedReciprocitySchwarzCausalRigidity

/-!
# One-sided retarded/advanced Schwarz no-go

The target-independent full-cokernel BM realization uses the causal propagator as its retarded
response and the zero map as its advanced response.  This module proves that the architecture,
not merely its chosen radial weight, is incompatible with physical causal Schwarz exchange:
an exchanged retarded/advanced pair with either side zero has both sides zero.

Consequently the canonical BM one-sided split is never Schwarz exchanged, because its radial
propagator is nonzero (indeed, its weight is non-Schwarz-real at every Xi copy).  Adding Green
reciprocity cannot repair the failure.  Thus this canonical full-cokernel realization is an exact
RH receiver but not an unconditional physical Einstein--Teukolsky producer.

The strongest positive survivor is the genuinely two-sided half-jump split
`(Delta / 2, -Delta / 2)`: the imported classification proves it is reciprocal and Schwarz
exchanged precisely for Peierls-skew, channel-Schwarz-odd `Delta`.  Universal literal BM incidence
for that surviving class is already equivalent to RH, so it cannot be supplied by relabelling the
one-sided canonical model.

`[NEW] [HB ROUTE KILL] [RETARDED/ADVANCED] [SCHWARZ EXCHANGE] [ONE-SIDED NO-GO] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Exact one-sided classification: causal Schwarz exchange with zero advanced response forces
the retarded response itself to vanish. -/
theorem hbXiPeierlsRetardedToAdvancedSchwarzExchange_zero_advanced_iff
    (Gret : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) :
    HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret 0 ↔ Gret = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro f
    have hf := congrArg hbXiPeierlsCanonicalChannelSchwarz (h f)
    rw [hbXiPeierlsCanonicalChannelSchwarz_involutive] at hf
    change Gret f = ((0, 0) : HBXiPeierlsCarrier)
    simpa using hf
  · rintro rfl
    intro f
    simp

/-- Reversed one-sided classification: causal Schwarz exchange with zero retarded response forces
the advanced response itself to vanish. -/
theorem hbXiPeierlsRetardedToAdvancedSchwarzExchange_zero_retarded_iff
    (Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) :
    HBXiPeierlsRetardedToAdvancedSchwarzExchange 0 Gadv ↔ Gadv = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro f
    have hf := h (hbXiPeierlsCanonicalChannelSchwarz f)
    rw [hbXiPeierlsCanonicalChannelSchwarz_involutive] at hf
    change Gadv f = ((0, 0) : HBXiPeierlsCarrier)
    simpa using hf.symm
  · rintro rfl
    intro f
    simp

/-- Minimal Green reciprocity adds no unilateral loophole: a reciprocal, Schwarz-exchanged pair
with zero advanced response is exactly the zero pair. -/
theorem hbXiPeierlsOneSidedZeroAdvancedMinimalPhysical_iff
    (Gret : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) :
    (HBXiPeierlsRetardedAdvancedReciprocal Gret 0 ∧
      HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret 0) ↔ Gret = 0 := by
  constructor
  · exact fun h =>
      (hbXiPeierlsRetardedToAdvancedSchwarzExchange_zero_advanced_iff Gret).1 h.2
  · rintro rfl
    constructor
    · intro f g
      simp only [LinearMap.zero_apply, map_zero]
    · intro f
      simp only [LinearMap.zero_apply, map_zero]

/-- The same exact classification holds when the retarded rather than advanced response vanishes. -/
theorem hbXiPeierlsOneSidedZeroRetardedMinimalPhysical_iff
    (Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) :
    (HBXiPeierlsRetardedAdvancedReciprocal 0 Gadv ∧
      HBXiPeierlsRetardedToAdvancedSchwarzExchange 0 Gadv) ↔ Gadv = 0 := by
  constructor
  · exact fun h =>
      (hbXiPeierlsRetardedToAdvancedSchwarzExchange_zero_retarded_iff Gadv).1 h.2
  · rintro rfl
    constructor
    · intro f g
      simp only [LinearMap.zero_apply, map_zero]
    · intro f
      simp only [LinearMap.zero_apply, map_zero]

/-- Route-killing specialization: the one-sided response split used by the canonical
target-independent full-cokernel BM realization is never Schwarz exchanged. -/
theorem hbXiPeierlsCanonicalFullCokernelOneSidedSplit_not_schwarzExchange
    (n : ℕ) (q : XiZeroCopy) :
    ¬ HBXiPeierlsRetardedToAdvancedSchwarzExchange
      (hbXiPeierlsPropagator n) 0 := by
  rw [hbXiPeierlsRetardedToAdvancedSchwarzExchange_zero_advanced_iff]
  intro hzero
  apply hbXiPeierlsRadialWeight_propagator_not_channelSchwarzOdd n q
  intro f
  rw [hbXiPeierlsWeightedPropagator_radialWeight n, hzero]
  simp

/-- Hence the canonical one-sided full-cokernel split cannot satisfy even the minimal conjunction
of Green reciprocity and causal Schwarz exchange. -/
theorem hbXiPeierlsCanonicalFullCokernelOneSidedSplit_not_minimallyPhysical
    (n : ℕ) (q : XiZeroCopy) :
    ¬ (HBXiPeierlsRetardedAdvancedReciprocal (hbXiPeierlsPropagator n) 0 ∧
      HBXiPeierlsRetardedToAdvancedSchwarzExchange
        (hbXiPeierlsPropagator n) 0) := by
  intro h
  exact hbXiPeierlsCanonicalFullCokernelOneSidedSplit_not_schwarzExchange n q h.2

end

end RHTower
