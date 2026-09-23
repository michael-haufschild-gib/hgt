import GaloisForLFunctions.HTGeometry.HerglotzGaugeTransfer
import GaloisForLFunctions.RHTower.XiExponentialDeckChargeBlindness

/-!
# Xi-exponential Herglotz-gauge universality

The rotated Xi exponential is unconditionally hypertranscendental at the upper end.  Every
nondegenerate Herglotz normalization is an invertible affine rational gauge, so the entire
one-parameter normalized family inherits the same differential-transcendence class.
-/

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

local instance xiHerglotzUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiHerglotzUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiHerglotzUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- **Xi-exponential Herglotz-gauge universality law.**  Every nonzero Herglotz
normalization of the rotated Xi exponential remains hypertranscendental over the rational
upper-end coordinate field. -/
theorem xiExponential_herglotzGauge_hypertranscendentalOver
    {c : ℂ} (hc : c ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
      (algebraMap ℂ upperEndMeroField c *
        (upperEndCoordinateMero +
          (1 + upperEndCoordinateMero ^ (2 : ℕ)) *
            xiExponentialRotatedUpperEndCarrier)) := by
  exact
    (hypertranscendentalOver_herglotzGauge_iff
      xiExponentialRotatedUpperEndCarrier hc).2
      xiExponentialRotatedUpperEndCarrier_hypertranscendentalOver

end

end RHTower
