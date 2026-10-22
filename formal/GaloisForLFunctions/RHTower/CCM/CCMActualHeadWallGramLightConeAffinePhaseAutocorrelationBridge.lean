import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeAffinePhaseSourceSewing
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadCompletedAutocorrelationProducer

/-!
# Affine wall-phase / completed-error autocorrelation bridge

The affine wall phase is source-faithful only if it remains attached to the actual Gamma-head
error current.  This file proves the exact identification: its finite phase-deficit producer is
the signed completed-error Gamma-boundary autocorrelation producer, on every actual head and on
the canonical Gamma--Slepian family.  Thus phase orientation and completed-error cancellation are
two coordinates of one RH-bearing quantity, rather than independent estimates that could silently
lose a term while being compared.

The equality does not prove the resulting source lower bound; that lower bound remains precisely
the literal reverse-prime condition on canonical heads.
-/

noncomputable section

namespace RHTower

/-- The coefficient-faithful affine wall phase and the signed completed-error Gamma boundary
current are exactly the same actual-head producer. -/
theorem ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_gammaBoundaryAutocorrelationProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer a u =
      ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer a u := by
  rw [ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_sourceQuadratic,
    ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer_eq_sourceQuadratic]

/-- On canonical finite Gamma--Slepian heads, the affine phase has the literal ground energy and
the already-certified nonnegative vanishing tail—no phase-side replacement is introduced. -/
theorem ccmRestrictedWeilCanonicalGroundHead_wallAffinePhaseSignedProducer_eq_ground_add_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ (2 : ℕ) +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_gammaBoundaryAutocorrelationProducer,
    ccmRestrictedWeilCanonicalGroundHead_gammaBoundaryAutocorrelationProducer_eq_ground_add_tail]

/-- The affine phase bridge does not weaken the RH-bearing condition: its Gamma-boundary form is
nonnegative exactly when the literal reverse-prime bound holds. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_wallAffinePhaseGammaBoundary_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [← ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_gammaBoundaryAutocorrelationProducer]
  exact ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_wallAffinePhaseSignedProducer_nonneg a n

end RHTower
