import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactAbelIntegrability
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.HolomorphicContactSymbolsExcludeInteriorZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerCombsHaveTheirAbelLimitAtTheBoundary

/-!
# Absolute logarithmic Abel integrability detects the closed zero width

Every positive damping is integrable exactly when the power parameter
lies in the closed zero-width range. Outside that range a zeta zero gives
an interior pole of the actual contact symbol, contradicting holomorphy
of the literal integral. Inside it the Abel limit is the reflected zero
pairing, including an attained boundary where ordinary convergence fails.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity

/-- A zero strictly beyond the power boundary prevents absolute
integrability for all positive logarithmic dampings. -/
theorem not_logarithmicAbelIntegrable_powerCombTail_of_zero
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hre : 1 - a < ρ.re) :
    ¬ LogarithmicAbelIntegrable (powerCombTail a) := by
  intro hc
  exact holomorphic_contact_symbol_excludes_interior_zero ha
    (by linarith only [ha2])
    (differentiableOn_powerContactMellin_of_abelIntegrable ha ha2 hc)
    (fun _ hs => oneSidedStepMellin_powerContact_initial ha ha2 hs) hzero hre

/-- All positive absolute Abel integrals exist exactly at and below the
zero-width boundary. -/
theorem logarithmicAbelIntegrable_powerCombTail_iff
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    LogarithmicAbelIntegrable (powerCombTail a) ↔
      a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2 := by
  constructor
  · intro hc
    have hw : SquareRootThreshold.zetaZeroWidth ≤ 1 / 2 - a := by
      apply (SquareRootThreshold.zetaZeroWidth_le_iff_re_le
        (by linarith only [ha2] : 0 ≤ 1 / 2 - a)).mpr
      intro ρ hρ
      have hzero : riemannZeta ρ = 0 := hρ.1
      by_contra hle
      have hgt : 1 - a < ρ.re := by linarith only [not_le.mp hle]
      exact not_logarithmicAbelIntegrable_powerCombTail_of_zero ha ha2 hzero hgt hc
    linarith only [hw]
  · intro haw
    exact logarithmicAbelIntegrable_of_strictGrowth
      (strictGrowth_powerCombTail_of_add_width_le_half ha ha2 haw)

/-- Whenever every positive absolute Abel integral exists, its normalized
limit is forced to be the reflected zero pairing. -/
theorem tendsto_logarithmicAbelMean_powerCombTail_of_abelIntegrable
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (hc : LogarithmicAbelIntegrable (powerCombTail a)) :
    Tendsto (logarithmicAbelMean (powerCombTail a)) (𝓝[>] 0) (𝓝 (powerTailZeroPairing a)) :=
  tendsto_logarithmicAbelMean_powerCombTail_of_add_width_le_half ha ha2
    ((logarithmicAbelIntegrable_powerCombTail_iff ha ha2).mp hc)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
