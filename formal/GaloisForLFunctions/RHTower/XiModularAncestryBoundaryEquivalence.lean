import GaloisForLFunctions.RHTower.XiJointAncestrySuperselection
import GaloisForLFunctions.RHTower.SourceHorizontalXiInformationEscapeLaw
import GaloisForLFunctions.RHTower.XiPrimeSeamSummableCalkinAggregate
import GaloisForLFunctions.RHTower.RouteRStrongApproximationCompactEscape

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Reflected prime-source measure class, closed sewing, all-prime Calkin compactness,
information tightness, and collective compactness are one local modular-ancestry condition. -/
theorem xiModularAncestryBoundary_tight_iff
    (q : XiZeroCopy) (p : Nat.Primes) {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    XiPrimePoissonReflectionSewing q.1 ↔
      let hstrip := xi_divisor_support_re_mem_open_unit q.1
      ((primePoissonMeasure (q.1 : ℂ).re (q.1 : ℂ).im hstrip.1 ≪
          primePoissonMeasure (1 - (q.1 : ℂ).re) (q.1 : ℂ).im
            (sub_pos.mpr hstrip.2)) ∧
        (primePoissonMeasure (1 - (q.1 : ℂ).re) (q.1 : ℂ).im
            (sub_pos.mpr hstrip.2) ≪
          primePoissonMeasure (q.1 : ℂ).re (q.1 : ℂ).im hstrip.1)) ∧
      OrbitwisePrimeSeamSummableCalkinAggregateCompact a (q.1 : ℂ) ∧
      ¬ SourceHorizontalXiAbelianInformationEscape q p ∧
      RouteRTwoThreeCanonicalStrongApproximationHasCompactEnvelope A
        (primeDepthBVWoldXiCenteredRate q.1) := by
  let hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hsew : XiPrimePoissonReflectionSewing q.1 ↔ (q.1 : ℂ).re = 1 / 2 := by
    rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
      xiDivisorSyndromeIsInternalOnly_iff_re_eq_half]
  have hmeasure :
      ((primePoissonMeasure (q.1 : ℂ).re (q.1 : ℂ).im hstrip.1 ≪
          primePoissonMeasure (1 - (q.1 : ℂ).re) (q.1 : ℂ).im
            (sub_pos.mpr hstrip.2)) ∧
        (primePoissonMeasure (1 - (q.1 : ℂ).re) (q.1 : ℂ).im
            (sub_pos.mpr hstrip.2) ≪
          primePoissonMeasure (q.1 : ℂ).re (q.1 : ℂ).im hstrip.1)) ↔
        (q.1 : ℂ).re = 1 / 2 :=
    primePoissonMeasure_reflection_mutuallyAbsolutelyContinuous_iff
      (q.1 : ℂ).re (q.1 : ℂ).im hstrip.1 hstrip.2
  have hcompact :
      OrbitwisePrimeSeamSummableCalkinAggregateCompact a (q.1 : ℂ) ↔
        (q.1 : ℂ).re = 1 / 2 :=
    orbitwisePrimeSeamSummableCalkinAggregateCompact_iff_re_eq_half
      a (q.1 : ℂ) ha hstrip
  have hescape :
      (¬ SourceHorizontalXiAbelianInformationEscape q p) ↔
        (q.1 : ℂ).re = 1 / 2 := by
    rw [sourceHorizontalXiAbelianInformationEscape_iff_re_ne_half]
    tauto
  have henvelope :
      RouteRTwoThreeCanonicalStrongApproximationHasCompactEnvelope A
          (primeDepthBVWoldXiCenteredRate q.1) ↔
        (q.1 : ℂ).re = 1 / 2 := by
    rw [routeRTwoThreeCanonicalStrongApproximation_hasCompactEnvelope_iff hA,
      primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  dsimp only
  rw [hsew, hmeasure, hcompact, hescape, henvelope]
  tauto

end

end RHTower
