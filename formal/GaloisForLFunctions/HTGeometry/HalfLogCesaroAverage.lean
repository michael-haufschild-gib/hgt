import Mathlib

/-!
# The half-log Cesàro average and its derivative

For a profile `F` on the half-line write

`Y(L) = ∫_0^L F`,  `P F(L) = 2L F(L) − Y(L)`,  `A(L) = Y(L) / (2√L)`.

The average `A` is normalised so that a profile `F ~ β/√L` gives `Y ~ 2β√L` and hence `A → β`, the
same limit as the half-log trace `H(L) = √L F(L)`.  Differentiating `A` produces the operator `P`
divided by a pure power:

`A'(L) = P F(L) / (4 L^{3/2})`.

So the source equation controls `A'`, an integrable quantity against `L^{-3/2}`, and convergence of
`A` follows.  This is the mechanism that produces the averaged trace.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- The primitive of a profile on the half-line. -/
noncomputable def halfLinePrimitive (F : ℝ → ℝ) (L : ℝ) : ℝ := ∫ x in (0 : ℝ)..L, F x

/-- The logarithmic Dirichlet operator `P F(L) = 2L F(L) − Y(L)`. -/
noncomputable def logDirichlet (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  2 * L * F L - halfLinePrimitive F L

/-- The half-log Cesàro average `A(L) = Y(L)/(2√L)`. -/
noncomputable def halfLogAverage (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  halfLinePrimitive F L / (2 * Real.sqrt L)

/-- The primitive differentiates to the profile. -/
theorem hasDerivAt_halfLinePrimitive {F : ℝ → ℝ} (hF : Continuous F) (L : ℝ) :
    HasDerivAt (halfLinePrimitive F) (F L) L :=
  intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
    (hF.stronglyMeasurableAtFilter _ _) hF.continuousAt

/-- **The derivative of the half-log average.**  Differentiating `Y/(2√L)` produces exactly the
logarithmic Dirichlet operator over `4L^{3/2}`. -/
theorem hasDerivAt_halfLogAverage {F : ℝ → ℝ} (hF : Continuous F) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (halfLogAverage F)
      (logDirichlet F L / (4 * L * Real.sqrt L)) L := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hY : HasDerivAt (halfLinePrimitive F) (F L) L := hasDerivAt_halfLinePrimitive hF L
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt L)) L :=
    Real.hasDerivAt_sqrt (ne_of_gt hL)
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt L))) L :=
    hs.const_mul 2
  have hne : 2 * Real.sqrt L ≠ 0 := by positivity
  have hdiv := hY.div hden hne
  have hval : (F L * (2 * Real.sqrt L) -
      halfLinePrimitive F L * (2 * (1 / (2 * Real.sqrt L)))) / (2 * Real.sqrt L) ^ 2
      = logDirichlet F L / (4 * L * Real.sqrt L) := by
    unfold logDirichlet
    have hsq2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
    field_simp
    linear_combination 4 * halfLinePrimitive F L * hsq2
  rwa [hval] at hdiv

/-- The average is the primitive against the half-log weight, so it tends to the same limit as the
half-log trace whenever both exist. -/
theorem halfLogAverage_eq {F : ℝ → ℝ} (L : ℝ) :
    halfLogAverage F L = halfLinePrimitive F L / (2 * Real.sqrt L) := rfl

end GaloisForLFunctions.HTGeometry
