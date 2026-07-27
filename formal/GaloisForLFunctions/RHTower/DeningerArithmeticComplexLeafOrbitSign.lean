import Mathlib.Data.Complex.Basic

/-!
# Complex-leaf orbit orientation

This module formalizes the unconditional scalar determinant core of
`DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN`: a nondegenerate complex-linear return
map on a complex line has positive real Lefschetz determinant.

No arithmetic-cohomology existence, zeta-zero, spectral, positivity, or
Riemann-hypothesis premise occurs.
-/

namespace GaloisForLFunctions.RHTower

/-- Coordinate formula for the real determinant of `1 - a` on a complex line. -/
theorem deningerComplexLeaf_returnDet_eq_normSq (a : ℂ) :
    (1 - a.re) ^ 2 + a.im ^ 2 = Complex.normSq (1 - a) := by
  simp [Complex.normSq]

/-- A nondegenerate complex-linear return map has positive real determinant. -/
theorem deningerComplexLeaf_returnDet_pos
    {a : ℂ} (ha : a ≠ 1) :
    0 < (1 - a.re) ^ 2 + a.im ^ 2 := by
  rw [deningerComplexLeaf_returnDet_eq_normSq]
  exact Complex.normSq_pos.mpr (sub_ne_zero.mpr ha.symm)

end GaloisForLFunctions.RHTower
