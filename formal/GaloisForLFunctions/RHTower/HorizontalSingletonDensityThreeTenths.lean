import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergThreeTenths
import GaloisForLFunctions.RHTower.HorizontalSimplicityTradeoffDensity

/-!
# Horizontal singleton fibres with the off-line moment `81/1000`

With `Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (81/1000) V`
(`eventually_offLineMoment_le_selberg_threeTenths`)
the overlap-deficit tradeoff `HD(1) − πμ/12` (`horizontalSingleton_density_of_moment`) gives
horizontal singleton fibres of lower density at least `HD(1) − 27π/4000 = 0.651…`.
-/

open Filter

namespace RHTower

/-- **Horizontal singleton fibres of lower density `HD(1) − 27π/4000`.** -/
theorem horizontalSingleton_density_threeTenths :
    Zeta23.ThmD.HD 1 - 27 * Real.pi / 4000 ≤ liminf xiSingletonFiberRatio atTop := by
  have h := horizontalSingleton_density_of_moment (μ := 81 / 1000) (by norm_num) (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_threeTenths
  rwa [show Real.pi * (81 / 1000) / 12 = 27 * Real.pi / 4000 by ring] at h

end RHTower
