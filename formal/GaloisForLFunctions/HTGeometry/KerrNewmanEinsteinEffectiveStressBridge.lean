import GaloisForLFunctions.HTGeometry.KerrNewmanEinsteinMaxwellAlgebra
import GaloisForLFunctions.HTGeometry.ClockDynamicsUnderdetermination

/-!
# Kerr--Newman canonical Maxwell source as effective stress

The explicit flat-background canonical Maxwell Einstein-form equation is an instance of the
corpus's generic effective-stress construction at unit coupling. This exact algebraic bridge does
not calculate a Kerr--Newman Einstein tensor or independently select a physical source.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The canonical flat Kerr--Newman Maxwell stress is exactly the unit-coupling effective stress
of the declared Einstein-tensor representative. -/
theorem kerrNewmanFlatLimit_canonicalMaxwellStress_eq_effectiveStress
    (cosmological electric magnetic : ℝ) :
    effectiveStressTensor 1 cosmological
      (kerrNewmanFlatLimitCanonicalEinsteinTensor cosmological electric magnetic)
      (kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2)) =
      kerrNewmanCanonicalMaxwellStress electric magnetic := by
  simp [effectiveStressTensor, kerrNewmanFlatLimitCanonicalEinsteinTensor]

/-- The generic unit-coupling effective-stress Einstein equation instantiates on the canonical
flat Kerr--Newman representative. -/
theorem kerrNewmanFlatLimit_effectiveStressEinsteinEquation
    (cosmological electric magnetic : ℝ) :
    kerrNewmanFlatLimitCanonicalEinsteinTensor cosmological electric magnetic +
        cosmological • kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2) =
      (1 : ℝ) • effectiveStressTensor 1 cosmological
        (kerrNewmanFlatLimitCanonicalEinsteinTensor cosmological electric magnetic)
        (kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2)) := by
  exact einsteinEquation_effectiveStressTensor 1 cosmological
    (kerrNewmanFlatLimitCanonicalEinsteinTensor cosmological electric magnetic)
    (kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2)) (by norm_num)

/-- Rewriting the generic effective-stress equation recovers the canonical Maxwell equation. -/
theorem kerrNewmanFlatLimit_canonicalMaxwellEinsteinEquation_via_effectiveStress
    (cosmological electric magnetic : ℝ) :
    kerrNewmanFlatLimitCanonicalEinsteinTensor cosmological electric magnetic +
        cosmological • kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2) =
      kerrNewmanCanonicalMaxwellStress electric magnetic := by
  rw [kerrNewmanFlatLimit_effectiveStressEinsteinEquation,
    kerrNewmanFlatLimit_canonicalMaxwellStress_eq_effectiveStress]
  simp

end GaloisForLFunctions.HTGeometry
