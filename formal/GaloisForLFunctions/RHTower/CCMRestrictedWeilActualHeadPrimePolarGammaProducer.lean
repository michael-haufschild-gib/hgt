import GaloisForLFunctions.RHTower.CCMActualHeadGammaAutocorrelationEnergy

/-!
# Signed prime--polar--Gamma producer on actual finite heads

This module replaces the abstract archimedean form contribution in the completed-error Route O
producer by the exact positive Gamma translation-defect energy of the literal physical head.
Prime atoms, polar continuum, completed endpoint, and Gamma continuum therefore remain coupled to
one actual autocorrelation profile. On canonical finite Gamma--Slepian heads, nonnegativity of this
producer is exactly the reverse-prime bound; no surrogate common-clock or prolate operator enters.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

namespace RHTower

/-- Signed prime--polar--Γ producer. Every non-scalar term is evaluated on the same literal
finite Γ--Slepian head and the completed-error cancellation remains intact. -/
def ccmRestrictedWeilActualHeadPrimePolarGammaProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  2 * gammaHardyPhaseRate 0 * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
    ccmActualHeadGammaAutocorrelationEnergy
      (ccmArchimedeanFormToAperture a u : SoninL2) +
    ccmActualHeadCompletedErrorQuadrature a
      (ccmArchimedeanFormToAperture a u)

theorem ccmRestrictedWeilActualHeadPrimePolarGammaProducer_eq_completedErrorProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadPrimePolarGammaProducer a u =
      ccmRestrictedWeilActualHeadCompletedErrorProducer a u := by
  unfold ccmRestrictedWeilActualHeadPrimePolarGammaProducer
    ccmRestrictedWeilActualHeadCompletedErrorProducer
  rw [ccmActualHeadGammaAutocorrelationEnergy_formDomain]
  ring

theorem ccmRestrictedWeilActualHeadPrimePolarGammaProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadPrimePolarGammaProducer a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilActualHeadPrimePolarGammaProducer_eq_completedErrorProducer,
    ccmRestrictedWeilActualHeadCompletedErrorProducer_eq_sourceQuadratic]

theorem ccmRestrictedWeilCanonicalGroundHead_primePolarGammaProducer_eq_ground_add_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilActualHeadPrimePolarGammaProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilActualHeadPrimePolarGammaProducer_eq_completedErrorProducer,
    ccmRestrictedWeilCanonicalGroundHead_actualHeadProducer_eq_ground_add_tail]

theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_primePolarGammaProducer_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilActualHeadPrimePolarGammaProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_actualHeadProducer_nonneg,
    ccmRestrictedWeilActualHeadPrimePolarGammaProducer_eq_completedErrorProducer]

end RHTower
