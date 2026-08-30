import GaloisForLFunctions.RHTower.SourceZeroHedenmalmOrientationRigidity
import GaloisForLFunctions.RHTower.SourceGammaNaturalitySharedGhostProducer
import GaloisForLFunctions.RHTower.RouteRTwoThreeGammaSingularCoronaProducer
import GaloisForLFunctions.RHTower.RiemannSourceForcedHorizontalVanishingFrontier

/-!
# Hedenmalm source equality as a multi-route descent law

One literal equality of the actual reflected Hedenmalm causal source flows is stronger than a
single receiver condition.  On one analytic-multiplicity Xi copy it simultaneously kills the
pre-scalar source-zero horizontal carrier, forces the selected two-prime Gamma naturality, flattens
Route R's coefficient-faithful singular corona, and vanishes the canonical Gamma/co-Poisson
boundary defect.  Prime labels, both reflection orientations, and multiplicity copies are retained.

The file does not assert the reflected-flow equality: its global form is RH-equivalent.  It records
the exact multi-gate consequence a genuine source proof of that equality would discharge.
-/

namespace RHTower

noncomputable section

/-- One reflected Hedenmalm source-flow equality is a multi-route source law: it removes the
pre-scalar horizontal carrier, forces the selected two-prime Gamma naturality, flattens Route R's
singular corona, and kills the canonical Gamma/co-Poisson defect. -/
theorem sourceZeroHedenmalmOrientationLaw_multiGateDescent
    (K : ℕ) (q : XiZeroCopy) (hsource : SourceZeroHedenmalmOrientationLaw q) :
    sourceZeroHorizontalResolutionCarrier K q = 0 ∧
      sourceZeroHorizontalTailLog q = 0 ∧
      (∀ p : Nat.Primes, sourceZeroHorizontalPrimeCarrier q p = 0) ∧
      sourceZeroHorizontalCarrierAt K q = 0 ∧
      sourceZeroHorizontalCarrierAt K (xiZeroCopyLineConjEquiv q) = 0 ∧
      FrankensteinSourceGammaNaturalSharedGhostDescendsAt q.1 ∧
      CCMRationalAdelicXiTwoThreeGammaSingularCoronaFlat q.1 ∧
      riemannSourceGammaCoPoissonHorizontalDefect q.1 = 0 := by
  have hline : (q.1 : ℂ).re = 1 / 2 :=
    (sourceZeroHedenmalmOrientationLaw_iff_re_eq_half q).1 hsource
  rcases sourceZeroHedenmalmOrientationLaw_annihilates_both_orientations K q hsource with
    ⟨hresolution, htail, hprime, hcarrier, hreflection⟩
  refine ⟨hresolution, htail, hprime, hcarrier, hreflection, ?_, ?_, ?_⟩
  · exact (frankensteinSourceGammaNaturalSharedGhostDescendsAt_iff q.1).2 hline
  · rw [twoThreeGammaSingularCoronaFlat_iff_centeredRate_eq_zero,
      primeDepthBVWoldXiCenteredRate_eq_zero_iff]
    exact hline
  · exact (riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff q.1).2 hline

end

end RHTower
