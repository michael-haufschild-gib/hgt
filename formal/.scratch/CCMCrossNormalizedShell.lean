import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureRieszTransport

open scoped InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

def scratch_normalizedCompletedCovarianceSource
    (a : SuzukiPositiveAperture) (eps : ℝ) : SoninL2 :=
  (‖suzukiTaRawDeficiency a eps‖ : ℂ) •
    suzukiTaMovableCompletedCovarianceSource a eps

theorem scratch_normalizedCompletedCovarianceSource_crossAperture_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    scratch_normalizedCompletedCovarianceSource b eps -
      scratch_normalizedCompletedCovarianceSource a eps =
      (‖suzukiTaRawDeficiency b eps‖ : ℂ) •
        suzukiApertureZeroExtendL2
          (suzukiWeilIntervalFormEmbedding b
            (suzukiTaRiesz_metricRenormalizedShell hab eps)) +
      ((‖suzukiTaRawDeficiency b eps‖ - ‖suzukiTaRawDeficiency a eps‖ : ℝ) : ℂ) •
        suzukiTaMovableCompletedCovarianceSource a eps +
      ((‖suzukiTaRawDeficiency b eps‖ : ℂ) *
        ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ)) •
        suzukiApertureZeroExtendL2
          (suzukiWeilIntervalCovariance b
            (suzukiWeilIntervalFormEmbedding b
              (ccmArchimedeanFormDomain_extension hab
                (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))))) := by
  let nb : ℝ := ‖suzukiTaRawDeficiency b eps‖
  let na : ℝ := ‖suzukiTaRawDeficiency a eps‖
  let S : SoninL2 := suzukiApertureZeroExtendL2
    (suzukiWeilIntervalFormEmbedding b
      (suzukiTaRiesz_metricRenormalizedShell hab eps))
  let P : SoninL2 := suzukiTaMovableCompletedCovarianceSource b eps
  let Q : SoninL2 := suzukiTaMovableCompletedCovarianceSource a eps
  let d : ℂ := ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ)
  let K : SoninL2 := suzukiApertureZeroExtendL2
    (suzukiWeilIntervalCovariance b
      (suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))))
  change (nb : ℂ) • P - (na : ℂ) • Q =
    (nb : ℂ) • S + ((nb - na : ℝ) : ℂ) • Q + ((nb : ℂ) * d) • K
  have hs : S = P - Q - d • K := by
    exact suzukiTaRiesz_metricRenormalizedShell_physical_eq hab eps
  have hp : P = S + Q + d • K := by
    rw [hs]
    module
  rw [hp]
  module

end RHTower
