import GaloisForLFunctions.RHTower.RouteRCompletionPhantomNoether
import GaloisForLFunctions.RHTower.RouteRCompletionMigrationDefect
import GaloisForLFunctions.RHTower.RouteRFixedTraceTailRoos
import GaloisForLFunctions.RHTower.CompleteResolutionCofinalConditioningLaw
import GaloisForLFunctions.RHTower.CompleteResolutionSharedGaugeReflectionAtlas

/-!
# The Xi completion-defect syndrome

The corpus supplies several apparently different descriptions of an off-line Xi divisor fibre:

* a source-provenance completion phantom;
* a nonzero fixed-tail Roos class and surviving exactness-flag defect;
* a conserved Noether orientation charge;
* divergent inverse conditioning of the complete Riemann source;
* failure of every shared-gauge reflection descent candidate.

This file proves that these are simultaneous shadows of one transverse completion defect.  It does
not postulate a mechanism annihilating that defect.  Its purpose is to prevent any one shadow from
being mistaken for an independent source of RH: a successful arithmetic law must exclude the whole
syndrome before scalarization, completion, gauge splitting, or observer recovery can launder it.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- An actual Xi divisor point regarded as a point of the complete-resolution critical strip. -/
def xiCompleteResolutionStripPoint
    (rho : XiDivisorSupport) : CompleteResolutionOpenCriticalStrip :=
  ⟨(rho : ℂ), xi_divisor_support_re_mem_open_unit rho⟩

/-- The complete source-defined syndrome carried by one off-line Xi divisor fibre.  Every field is
an independently constructed corpus shadow of the same horizontal transverse charge. -/
structure XiCompletionDefectSyndrome (rho : XiDivisorSupport) : Prop where
  completionPhantom : RouteRPrimeGammaXiCompletionPhantom rho
  completionEscapeClass_nonzero :
    routeRPrimeGammaXiCompletionEscapeClass rho ≠ 0
  noetherOrientationCharge_nonzero :
    routeRPrimeGammaXiNoetherOrientationCharge rho ≠ 0
  tailRoosClass_nonzero :
    routeRPrimeGammaXiDiagonalTailRoosClass rho ≠ 0
  exactnessFlag_survives :
    routeRTailRoosExactnessFlag ∈ ExFlag.survival
      (routeRPrimeGammaFixedGradeTailLanding
        (2 * (rho : ℂ).re - 1)
        routeRPrimeGammaFisherSourceBoundary)
  inverseConditioning_blowup :
    Tendsto
      (fun K : ℕ =>
        ‖completeResolutionReflectionSourceDisplacement K
          (xiCompleteResolutionStripPoint rho)‖⁻¹)
      atTop atTop
  sharedGauge_failure :
    ∀ (K : ℕ) (C : SharedGaugeReflectionDescentCandidate),
      ¬ CompleteResolutionForwardGood K C
          (xiCompleteResolutionStripPoint rho) ∨
        ¬ CompleteResolutionReflectedGood K C
          (xiCompleteResolutionStripPoint rho) ∨
        ¬ CompleteResolutionSharedGauge C
          (xiCompleteResolutionStripPoint rho)

/-- **Syndrome classification.**  One actual Xi divisor fibre carries all completion-defect
shadows simultaneously exactly when it is off the critical line. -/
theorem xiCompletionDefectSyndrome_iff_re_ne_half
    (rho : XiDivisorSupport) :
    XiCompletionDefectSyndrome rho ↔ (rho : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro h
    exact (routeRPrimeGammaXiCompletionPhantom_iff_re_ne_half rho).1
      h.completionPhantom
  · intro hoff
    refine {
      completionPhantom :=
        (routeRPrimeGammaXiCompletionPhantom_iff_re_ne_half rho).2 hoff
      completionEscapeClass_nonzero := ?_
      noetherOrientationCharge_nonzero := ?_
      tailRoosClass_nonzero := ?_
      exactnessFlag_survives := ?_
      inverseConditioning_blowup := ?_
      sharedGauge_failure := ?_
    }
    · exact
        (routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho).not.mpr
          hoff
    · exact
        (routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).not.mpr
          hoff
    · exact
        (routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_re_eq_half rho).not.mpr
          hoff
    · exact
        (routeRPrimeGammaXiCompletionDefect_survives_iff_re_ne_half rho).2 hoff
    · exact
        tendsto_inv_norm_completeResolutionReflectionSourceDisplacement_atTop
          (xiCompleteResolutionStripPoint rho) hoff
    · intro K C
      let s : CompleteResolutionOffLineStrip :=
        ⟨xiCompleteResolutionStripPoint rho, hoff⟩
      exact completeResolution_sharedGaugeReflection_failure_at K C s

/-- Global absence of the simultaneous completion-defect syndrome. -/
def XiCompletionDefectSyndromeFree : Prop :=
  ∀ rho : XiDivisorSupport, ¬ XiCompletionDefectSyndrome rho

/-- RH is exactly global absence of the full syndrome, not merely absence of one chosen shadow. -/
theorem xiCompletionDefectSyndromeFree_iff_riemannHypothesis :
    XiCompletionDefectSyndromeFree ↔ RiemannHypothesis := by
  rw [← routeRPrimeGammaXiGlobalNoetherOrientationChargeFree_iff_riemannHypothesis]
  constructor
  · intro hfree rho
    by_contra hcharge
    have hoff : (rho : ℂ).re ≠ 1 / 2 :=
      (routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).not.mp
        hcharge
    exact hfree rho ((xiCompletionDefectSyndrome_iff_re_ne_half rho).2 hoff)
  · intro hcharge rho hsyndrome
    exact hsyndrome.noetherOrientationCharge_nonzero (hcharge rho)

/-- Contrapositive existence form: failure of RH is witnessed by one fibre carrying the complete
defect syndrome. -/
theorem not_riemannHypothesis_iff_exists_xiCompletionDefectSyndrome :
    ¬ RiemannHypothesis ↔
      ∃ rho : XiDivisorSupport, XiCompletionDefectSyndrome rho := by
  constructor
  · intro hnot
    by_contra hexists
    push Not at hexists
    exact hnot
      (xiCompletionDefectSyndromeFree_iff_riemannHypothesis.mp hexists)
  · rintro ⟨rho, hsyndrome⟩ hRH
    exact
      (xiCompletionDefectSyndromeFree_iff_riemannHypothesis.mpr hRH rho)
        hsyndrome

end

end RHTower
