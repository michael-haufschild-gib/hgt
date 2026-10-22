import GaloisForLFunctions.RHTower.IharaBlockSelector
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoordinateCutoffCovariance

/-! # Canonical singleton-consumer witnesses in the Riemann tower -/

namespace GaloisForLFunctions.RHTower

/-- The zero spectral parameter obeys the unit Ihara block bound. -/
theorem blockSpectralBound_zero : blockSpectralBound 1 0 := by
  norm_num [blockSpectralBound]

/-- Every threshold has its canonical sharp event-adapted cutoff. -/
theorem eventAdaptedCutoff (threshold : ℝ) :
    EventAdaptedCutoff (fun L => if L ≤ threshold then 0 else 1) threshold := by
  constructor
  · intro L hL
    simp [hL]
  intro L hL
  simp [show ¬ L ≤ threshold by linarith]

end GaloisForLFunctions.RHTower
