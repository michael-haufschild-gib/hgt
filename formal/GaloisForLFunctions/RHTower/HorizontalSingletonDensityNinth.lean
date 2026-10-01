import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergNinth
import GaloisForLFunctions.RHTower.HorizontalSimplicityTradeoffDensity

/-!
# Horizontal singleton fibres with the off-line moment `7/50`

With `Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (7/50) V` (`eventually_offLineMoment_le_selberg_ninth`) the
overlap-deficit tradeoff `HD(1) − πμ/12` (`horizontalSingleton_density_of_moment`) gives horizontal
singleton fibres of lower density at least `HD(1) − 7π/600 = 0.636…`.
-/

open Filter

namespace RHTower

/-- **Horizontal singleton fibres of lower density `HD(1) − 7π/600`.** -/
theorem horizontalSingleton_density_ninth :
    Zeta23.ThmD.HD 1 - 7 * Real.pi / 600 ≤ liminf xiSingletonFiberRatio atTop := by
  have h := horizontalSingleton_density_of_moment (μ := 7 / 50) (by norm_num) (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_ninth
  rwa [show Real.pi * (7 / 50) / 12 = 7 * Real.pi / 600 by ring] at h

end RHTower
