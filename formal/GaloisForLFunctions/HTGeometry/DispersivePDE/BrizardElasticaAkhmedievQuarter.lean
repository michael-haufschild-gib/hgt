import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherGalilean
import Mathlib.Tactic

/-!
# The paper's quarter-angle Akhmediev specialization

Figure 1 and the `μ=0` endpoint of equation (37) use `φ=π/4`.  The resulting modulation frequency
and wave number are both exactly one, so the spatial period is `2π`; all peak and pole-gap results
therefore acquire closed radical forms.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def quarterBreatherAngle : BreatherAngle :=
  ⟨Real.pi / 4, by
    constructor
    · positivity
    · nlinarith [Real.pi_pos]⟩

theorem quarterAkhmedievOmega : akhmedievOmega quarterBreatherAngle = 1 := by
  rw [akhmedievOmega, quarterBreatherAngle]
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]

theorem quarterAkhmedievWaveNumber : akhmedievWaveNumber quarterBreatherAngle = 1 := by
  rw [akhmedievWaveNumber, quarterBreatherAngle, Real.sin_pi_div_four]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem quarterAkhmedievSpatialPeriod :
    akhmedievSpatialPeriod quarterBreatherAngle = 2 * Real.pi := by
  rw [akhmedievSpatialPeriod, quarterAkhmedievWaveNumber]
  ring

theorem quarterAkhmedievDenominatorGap :
    akhmedievDenominator quarterBreatherAngle 0 0 = 1 - Real.sqrt 2 / 2 := by
  rw [akhmedievDenominator_center, quarterBreatherAngle, Real.cos_pi_div_four]

theorem quarterAkhmedievCenterNorm :
    ‖akhmedievBreather quarterBreatherAngle 0 0‖ =
      (1 + Real.sqrt 2) / Real.sqrt 2 := by
  rw [norm_akhmedievBreather_center, quarterBreatherAngle, Real.cos_pi_div_four]
  ring

theorem quarterAkhmedievGlobalPeak (ξ τ : ℝ) :
    ‖akhmedievBreather quarterBreatherAngle ξ τ‖ ≤
      (1 + Real.sqrt 2) / Real.sqrt 2 := by
  rw [← quarterAkhmedievCenterNorm]
  exact norm_akhmedievBreather_le_center quarterBreatherAngle ξ τ

theorem quarterAkhmedievSpatialPeriodic (ξ τ : ℝ) :
    akhmedievBreather quarterBreatherAngle (ξ + 2 * Real.pi) τ =
      akhmedievBreather quarterBreatherAngle ξ τ := by
  rw [← quarterAkhmedievSpatialPeriod]
  exact akhmedievBreather_periodic quarterBreatherAngle ξ τ

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
