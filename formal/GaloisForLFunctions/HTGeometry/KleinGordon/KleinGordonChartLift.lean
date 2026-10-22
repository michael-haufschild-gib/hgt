import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonUnitSpeed

/-!
# The spacetime chart

The corpus reads fields in coordinates: a spacetime is `Fin (d+1) → ℝ`, and the wave operator is
built from `coordPartial`, the derivative along `Pi.single j 1`. The construction lives instead on
`ℝ × EuclideanSpace ℝ (Fin d)`, so the two have to be matched.

The matching is a linear isomorphism, and what it costs is the bookkeeping of this file: moving one
coordinate of the chart moves either the time or exactly one spatial direction, and the spatial
directions of the chart are the standard orthonormal basis rescaled by `(2π)⁻¹` — the rescaling that
makes the propagation speed one.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

/-! ## The chart -/

/-- The spatial direction of the chart: the `i`-th standard vector. -/
noncomputable def kgDir (d : ℕ) (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (Pi.single i 1)

theorem kgDir_eq_basisFun (d : ℕ) (i : Fin d) :
    kgDir d i = EuclideanSpace.basisFun (Fin d) ℝ i := by
  rw [EuclideanSpace.basisFun_apply]
  ext j
  simp [kgDir, PiLp.single_apply]

/-- The spatial point of the chart, rescaled so that the propagation speed is one. -/
noncomputable def kgSpatial (d : ℕ) (y : Fin (d + 1) → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (2 * Real.pi)⁻¹ • (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => y i.succ)

/-- Moving the time coordinate does not move the spatial point. -/
theorem kgSpatial_update_zero (d : ℕ) (y : Fin (d + 1) → ℝ) (r : ℝ) :
    kgSpatial d (Function.update y 0 r) = kgSpatial d y := by
  have hfun : (fun i : Fin d => Function.update y 0 r i.succ) = fun i : Fin d => y i.succ := by
    funext i
    exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
  rw [kgSpatial, kgSpatial, hfun]

/-- Moving a spatial coordinate moves the spatial point along the rescaled direction. -/
theorem kgSpatial_update_succ (d : ℕ) (y : Fin (d + 1) → ℝ) (i : Fin d) (r : ℝ) :
    kgSpatial d (Function.update y i.succ r)
      = kgSpatial d y + (r - y i.succ) • ((2 * Real.pi)⁻¹ • kgDir d i) := by
  have hpi : (fun j : Fin d => Function.update y i.succ r j.succ)
      = (fun j : Fin d => y j.succ) + (r - y i.succ) • (Pi.single i (1 : ℝ)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one]
      ring
    · have hne : j.succ ≠ i.succ := fun hcontra => hj (Fin.succ_injective d hcontra)
      simp only [Function.update_of_ne hne, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero, add_zero]
  rw [kgSpatial, kgSpatial, hpi, map_add, map_smul, kgDir, smul_add]
  congr 1
  rw [smul_comm]

/-- The field of the chart: the real probe read in coordinates. -/
noncomputable def kgChartField {N : ℕ} {d : ℕ}
    (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (y : Fin (d + 1) → ℝ) : ℝ :=
  kgRealField a G₀ (y 0) (kgSpatial d y)

theorem kgChartField_update_zero {N d : ℕ} (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (y : Fin (d + 1) → ℝ) (r : ℝ) :
    kgChartField a G₀ (Function.update y 0 r) = kgRealField a G₀ r (kgSpatial d y) := by
  rw [kgChartField, kgSpatial_update_zero, Function.update_self]

theorem kgChartField_update_succ {N d : ℕ} (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (y : Fin (d + 1) → ℝ) (i : Fin d) (r : ℝ) :
    kgChartField a G₀ (Function.update y i.succ r)
      = kgRealField a G₀ (y 0)
        (kgSpatial d y + (r - y i.succ) • ((2 * Real.pi)⁻¹ • kgDir d i)) := by
  rw [kgChartField, kgSpatial_update_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]

end GaloisForLFunctions.HTGeometry
