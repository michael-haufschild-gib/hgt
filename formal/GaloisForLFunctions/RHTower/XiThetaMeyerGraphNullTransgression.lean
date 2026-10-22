import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHalfDensityXiGraphClosure
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniFluxPolarization

/-!
# Xi theta--Meyer graph-null transgression

The explicit Meyer graph-null sequence keeps one Xi evaluation fixed while its canonical
half-density completion norm decays exponentially.  This module identifies that decay rate with
the normalized rank-two Green flux of the genuine compact theta divisor eigenmode.

Thus compact-source non-adjointness and cofinal-source nonclosability are quantitatively the same
defect: after the positive theta mass-energy calibration, the squared Green flux is the exact
exponent governing collapse of the Meyer completion coordinate.
-/

open Complex

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- The normalized compact theta Green flux is the exact square-root rate of the explicit Meyer
graph-null collapse. -/
theorem norm_deningerMeyerHalfDensityXiGraphNullSequence_eq_exp_normalizedThetaFluxSq
    (q : XiZeroCopy) (n : ℕ) :
    ‖deningerMeyerHalfDensityCompletionMk
        (deningerMeyerHalfDensityXiGraphNullSequence q.1 n)‖ =
      Real.exp
          (-((n : ℝ) *
            (thetaXiRankTwoBoundaryFlux q /
              (2 * (thetaSource.mass * thetaXiRootEnergy q))) ^ (2 : ℕ))) *
        ‖deningerMeyerHalfDensityCompletionMk
          deningerMeyerLogGaussianCohomologyClass‖ := by
  rw [norm_deningerMeyerHalfDensityXiGraphNullSequence]
  congr 2
  rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate,
    deningerMeyerHalfDensityXiHorizontalRate,
    primeDepthBVWoldXiCenteredRate]
  have hmass : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
  have henergy : thetaXiRootEnergy q ≠ 0 := (thetaXiRootEnergy_pos q).ne'
  field_simp [hmass, henergy]

end


end RHTower
