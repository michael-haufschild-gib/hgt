import Mathlib

/-!
# Complex-leaf orbit orientation

This module formalizes the unconditional determinant core of
`DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN`: a nondegenerate complex-linear return
map on a complex line has positive real Lefschetz determinant.  The scalar
coordinate identity is bridged to the genuine real two-plane determinant of
the underlying real-linear endomorphism, and the same positivity holds for
every nondegenerate iterate.

No arithmetic-cohomology existence, zeta-zero, spectral, positivity, or
Riemann-hypothesis premise occurs.
-/

namespace GaloisForLFunctions.RHTower

/-- Coordinate formula for the real determinant of `1 - a` on a complex line. -/
theorem deningerComplexLeaf_returnDet_eq_normSq (a : ℂ) :
    (1 - a.re) ^ (2 : ℕ) + a.im ^ (2 : ℕ) = Complex.normSq (1 - a) := by
  simp [Complex.normSq]
  ring

/-- A nondegenerate complex-linear return map has positive real determinant. -/
theorem deningerComplexLeaf_returnDet_pos
    {a : ℂ} (ha : a ≠ 1) :
    0 < (1 - a.re) ^ (2 : ℕ) + a.im ^ (2 : ℕ) := by
  rw [deningerComplexLeaf_returnDet_eq_normSq]
  exact Complex.normSq_pos.mpr (sub_ne_zero.mpr ha.symm)

/-! ## The real two-plane determinant of a complex-linear return map -/

/-- Multiplication by a complex number, as a real-linear endomorphism of the complex line. -/
noncomputable def complexLeafReturn (a : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := a * z
  map_add' x y := by ring
  map_smul' r z := by
    simp only [Complex.real_smul, RingHom.id_apply]
    ring

@[simp]
theorem complexLeafReturn_apply (a z : ℂ) : complexLeafReturn a z = a * z := rfl

/-- Complex-linear return maps compose by multiplication of their multipliers. -/
theorem complexLeafReturn_pow (a : ℂ) (k : ℕ) :
    complexLeafReturn a ^ k = complexLeafReturn (a ^ k) := by
  induction k with
  | zero =>
      ext z
      simp [complexLeafReturn]
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      ext z
      simp [complexLeafReturn]
      ring

/-- **Real two-plane determinant of complex multiplication.**  In the oriented real basis
`1, i` the matrix of multiplication by `a` is `[[re a, -im a], [im a, re a]]`, whose
determinant is the norm square. -/
theorem det_complexLeafReturn (a : ℂ) :
    LinearMap.det (complexLeafReturn a) = Complex.normSq a := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.normSq_apply]

/-- Subtracting the return map from the identity is again a complex-linear return map. -/
theorem id_sub_complexLeafReturn (a : ℂ) :
    (LinearMap.id : ℂ →ₗ[ℝ] ℂ) - complexLeafReturn a = complexLeafReturn (1 - a) := by
  ext z
  simp [complexLeafReturn]
  ring

/-- The real Lefschetz determinant of a complex-linear return map is `|1 - a|²`. -/
theorem det_id_sub_complexLeafReturn (a : ℂ) :
    LinearMap.det ((LinearMap.id : ℂ →ₗ[ℝ] ℂ) - complexLeafReturn a)
      = (1 - a.re) ^ (2 : ℕ) + a.im ^ (2 : ℕ) := by
  rw [id_sub_complexLeafReturn, det_complexLeafReturn,
    deningerComplexLeaf_returnDet_eq_normSq]

/-- **Positive leafwise orbit sign.**  A nondegenerate complex-linear return map on a complex
line has strictly positive real Lefschetz determinant. -/
theorem det_id_sub_complexLeafReturn_pos {a : ℂ} (ha : a ≠ 1) :
    0 < LinearMap.det ((LinearMap.id : ℂ →ₗ[ℝ] ℂ) - complexLeafReturn a) := by
  rw [det_id_sub_complexLeafReturn]
  exact deningerComplexLeaf_returnDet_pos ha

/-- The leafwise orbit sign is `+1`. -/
theorem sign_det_id_sub_complexLeafReturn {a : ℂ} (ha : a ≠ 1) :
    Real.sign (LinearMap.det ((LinearMap.id : ℂ →ₗ[ℝ] ℂ) - complexLeafReturn a)) = 1 :=
  Real.sign_of_pos (det_id_sub_complexLeafReturn_pos ha)

/-- **Every nondegenerate iterate has positive sign.**  The `k`-th iterate of a complex-linear
return map is again complex-linear, so nondegeneracy `a ^ k ≠ 1` already forces the sign. -/
theorem sign_det_id_sub_complexLeafReturn_pow {a : ℂ} {k : ℕ} (ha : a ^ k ≠ 1) :
    Real.sign
        (LinearMap.det ((LinearMap.id : ℂ →ₗ[ℝ] ℂ) - complexLeafReturn a ^ k)) = 1 := by
  rw [complexLeafReturn_pow]
  exact sign_det_id_sub_complexLeafReturn ha

end GaloisForLFunctions.RHTower
