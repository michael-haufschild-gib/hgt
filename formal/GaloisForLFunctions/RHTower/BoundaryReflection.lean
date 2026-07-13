import GaloisForLFunctions.RHTower.BoundaryModulus
import GaloisForLFunctions.RHTower.CanonicalBranch

/-!
# Boundary normalization and functional-equation reflection

This module connects the scalar boundary normalization of a prime Bohr
coordinate with the fixed locus of the functional-equation line reflection.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A prime Bohr coordinate is on the boundary-normalized unit circle exactly
when the functional-equation line reflection fixes the exponent. -/
@[aesop norm simp]
theorem diagonalBoundary_unit_norm_iff_lineReflection_fixed (p : ℝ) (hp : 1 < p) (s : ℂ) :
    ‖boundaryUnitNormalize p ((p : ℂ) ^ (-s))‖ = 1 ↔
      RHTower.lineReflection (1 / 2) s = s := by
  rw [diagonalBoundary_unit_norm_iff p hp s]
  constructor
  · intro hs
    exact RHTower.lineReflection_eq_self hs
  · intro hfix
    have hre := congrArg Complex.re hfix
    rw [RHTower.lineReflection_re] at hre
    norm_num at hre
    linarith

end

end GaloisForLFunctions
