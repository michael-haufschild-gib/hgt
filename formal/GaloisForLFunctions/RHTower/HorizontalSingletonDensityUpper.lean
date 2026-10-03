import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper
import GaloisForLFunctions.RHTower.HorizontalSimplicityTradeoffDensity

/-!
# Horizontal singleton fibres with the off-line moment `67/1000`

With `Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (67/1000) V`
(`eventually_offLineMoment_le_selberg_upper`)
the overlap-deficit tradeoff `HD(1) − πμ/12` (`horizontalSingleton_density_of_moment`) gives
horizontal singleton fibres of lower density at least `HD(1) − 67π/12000 = 0.655…`.
-/

open Filter

namespace RHTower

/-- **Horizontal singleton fibres of lower density `HD(1) − 67π/12000`.** -/
theorem horizontalSingleton_density_upper :
    Zeta23.ThmD.HD 1 - 67 * Real.pi / 12000 ≤ liminf xiSingletonFiberRatio atTop := by
  have h := horizontalSingleton_density_of_moment (μ := 67 / 1000) (by norm_num) (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  rwa [show Real.pi * (67 / 1000) / 12 = 67 * Real.pi / 12000 by ring] at h

end RHTower
