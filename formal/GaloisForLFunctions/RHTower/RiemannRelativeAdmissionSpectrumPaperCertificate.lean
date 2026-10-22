import GaloisForLFunctions.RHTower.RiemannRelativeAdmissionSpectrumUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalSourceToXiLanding
import GaloisForLFunctions.RHTower.MobiusThetaComplexSourceToXiLanding
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittHellingerBetaRelativeResidueTransgression

/-!
# Certificate for the relative admission-spectrum paper

This leaf imports every load-bearing source, transport, admission-spectrum, and completed-incidence
module used by the paper.  Its capstone packages the new cross-route result: the two analytic
reflection sources have different admission spectra, and no regular linear profile transport can
intertwine them at any nonzero centered-strip displacement.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- The new paper core: exact spectrum mismatch together with the pointwise singularity theorem
for every nonzero centered-strip displacement. -/
theorem riemannRelativeAdmissionSpectrumPaperCore (x : ℝ) :
    hedenmalmBorelRelativeAdmissionSpectrum x ≠
        eulerPrimitiveRelativeAdmissionSpectrum ∧
      ∀ a : ℝ, |a| < 1 / 2 → a ≠ 0 →
        ¬ ∃ T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ),
          HedenmalmEulerReflectionL2TransportAt T x a := by
  constructor
  · exact hedenmalmBorelRelativeAdmissionSpectrum_ne_eulerPrimitive x
  · intro a ha ha0
    exact not_hedenmalmEulerReflectionL2TransportAt x ha ha0

end

end RHTower
