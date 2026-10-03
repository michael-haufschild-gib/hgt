import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergSeventh
import GaloisForLFunctions.RHTower.HorizontalSimplicityTradeoffDensity

/-!
# Horizontal singleton fibres with the off-line moment `3/25`

With `Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (3/25) V` (`eventually_offLineMoment_le_selberg_seventh`)
the overlap-deficit tradeoff `HD(1) − πμ/12` (`horizontalSingleton_density_of_moment`) gives
horizontal singleton fibres of lower density at least `HD(1) − π/100 = 0.641…`.
-/

open Filter

namespace RHTower

/-- **Horizontal singleton fibres of lower density `HD(1) − π/100`.** -/
theorem horizontalSingleton_density_seventh :
    Zeta23.ThmD.HD 1 - Real.pi / 100 ≤ liminf xiSingletonFiberRatio atTop := by
  have h := horizontalSingleton_density_of_moment (μ := 3 / 25) (by norm_num) (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_seventh
  rwa [show Real.pi * (3 / 25) / 12 = Real.pi / 100 by ring] at h

end RHTower
