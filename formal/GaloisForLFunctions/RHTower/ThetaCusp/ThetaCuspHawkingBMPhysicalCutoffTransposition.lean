import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCutoffSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGeneralTemporalTransposition

/-! Exact finite direct-minus-image transposition for the literal compact physical source. -/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMGeneralTemporalTransposition D4BMModularCore D4BMHorizon
noncomputable section

/-- Each strict compact physical cutoff of the actual reduced source is transposed by the
literal direct-minus-image wave kernel with no reflected source vertex. -/
theorem physicalCutoffSource_dirichlet_transposition (q : XiZeroCopy) (u y X k : ℝ)
    (hy : y < 0) (n : ℕ) (s a : ℂ) :
    (∫ p : ℝ × ℝ, dirichletWaveTest q u y X k (physicalCutoffSource n s a) p) =
      fullSquarePotential q ![X, Real.exp k] * physicalCutoffSource n s a (u, y) := by
  exact physical_dirichlet_wave_transposition q u y X k hy (physicalCutoffSource n s a)
    (physicalCutoffSource_smooth n s a) (physicalCutoffSource_hasCompactSupport n s a)
    (physicalCutoffSource_tsupport_subset_physical n s a)

end
end RHTower.D4BMJointSource
