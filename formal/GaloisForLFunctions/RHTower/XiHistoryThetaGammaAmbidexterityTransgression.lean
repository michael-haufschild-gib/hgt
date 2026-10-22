import GaloisForLFunctions.RHTower.XiDualityDaggerHistoryTransgression
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixRelativeReflectionFraming
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniFluxPolarization

/-!
# Xi history--theta--Gamma ambidexterity transgression

Three independently constructed defects are one signed scalar before any squaring or orbit
averaging:

* metric holonomy between two executable source histories representing one semantic repair;
* normalized rank-two Green flux of the genuine compact theta eigenmode; and
* inverse-Cayley fixed-frame skew of the transported Gamma-six reflection carrier.

Thus source-history confluence, compact spectral boundary neutrality, and fixed-frame Gamma
adjunction are not merely equivalent zero tests.  They are exact presentations of one relative
duality--dagger cocycle, with logarithmic clock normalization retained.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open ConstitutiveCriticalCompletionMechanics
open HedenmalmThetaSource

/-- Source-history holonomy is the normalized compact-theta Green flux at the same prime clock. -/
theorem actualRepairHistoryDefect_eq_normalizedThetaFlux
    (N : ℕ) (p : Nat.Primes) (q : XiZeroCopy) :
    actualRepairOrientationPotential N (p : ℕ) (q.1 : ℂ) (left (N + 1)) -
        actualRepairOrientationPotential N (p : ℕ) (q.1 : ℂ) (right (N + 1)) =
      -Real.log (p : ℕ) * thetaXiRankTwoBoundaryFlux q /
        (thetaSource.mass * thetaXiRootEnergy q) := by
  have hmass : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
  have henergy : thetaXiRootEnergy q ≠ 0 := (thetaXiRootEnergy_pos q).ne'
  rw [actualRepairHistoryDefect_eq_shellTransferEntropy,
    shellTransferEntropy_eq,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate,
    primeDepthBVWoldXiCenteredRate]
  field_simp [hmass, henergy]
  ring

/-- The same source-history holonomy is inverse-Cayley skew of the fixed Gamma-six source frame. -/
theorem actualRepairHistoryDefect_eq_artanh_fixedMetricSkewRatio
    (N : ℕ) (p : Nat.Primes) (q : XiZeroCopy) :
    actualRepairOrientationPotential N (p : ℕ) (q.1 : ℂ) (left (N + 1)) -
        actualRepairOrientationPotential N (p : ℕ) (q.1 : ℂ) (right (N + 1)) =
      Real.artanh
        (sourceHorizontalGammaSixFixedMetricSkewRatio
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1)) := by
  calc
    _ = -Real.log (p : ℕ) * thetaXiRankTwoBoundaryFlux q /
        (thetaSource.mass * thetaXiRootEnergy q) :=
      actualRepairHistoryDefect_eq_normalizedThetaFlux N p q
    _ = _ :=
      (sourceHorizontalGammaSixPrimePhysical_artanh_fixedMetricSkewRatio_eq_thetaFlux
        q p).symm

end


end RHTower
