import GaloisForLFunctions.HTGeometry.KleinGordonChartLift

/-!
# The partial derivatives of the chart field

The corpus's differentiability instrument asks for the derivative of `a ↦ u (update x j a)` at each
coordinate. Here those derivatives are computed: the zeroth coordinate is the time derivative of the
probe, and the `i`-th spatial coordinate is its derivative along the rescaled direction, shifted so
that the parameter starts at the current value of the coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## Derivatives of the real probe -/

variable (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)

theorem differentiableAt_kgRealField_time (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (x : E)
    (t : ℝ) : DifferentiableAt ℝ (fun r : ℝ => kgRealField a G₀ r x) t :=
  (hasDerivAt_re (hasDerivAt_kgFlowField hN a G₀ x t)).differentiableAt

theorem differentiableAt_kgRealField_dir (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ)
    (x v : E) (s : ℝ) :
    DifferentiableAt ℝ (fun q : ℝ => kgRealField a G₀ t (x + q • v)) s :=
  (hasDerivAt_re
    ((hasDerivAt_kgSynthesis_dir_synthesis
      ((continuous_kgFlowDensity a G₀ t).aestronglyMeasurable)
      (integrable_kgFlowDensity a G₀ hN t)
      (integrable_kgFreq_mul_kgFlowDensity a G₀ hN t) x v s))).differentiableAt

/-! ## The chart partials -/

variable {d : ℕ}

/-- The time partial of the chart field. -/
noncomputable def kgChartTimePartial (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (y : Fin (d + 1) → ℝ) : ℝ :=
  deriv (fun r : ℝ => kgRealField a G₀ r (kgSpatial d y)) (y 0)

/-- The `i`-th spatial partial of the chart field. -/
noncomputable def kgChartSpacePartial (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (i : Fin d) (y : Fin (d + 1) → ℝ) : ℝ :=
  deriv (fun s : ℝ => kgRealField a G₀ (y 0)
    (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i))) 0

/-- The partial derivatives of the chart field, indexed by the chart coordinates. -/
noncomputable def kgChartPartial (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (j : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (kgChartTimePartial a G₀) (fun i => kgChartSpacePartial a G₀ i) j

theorem kgChartPartial_zero (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) :
    kgChartPartial a G₀ 0 = kgChartTimePartial a G₀ := rfl

theorem kgChartPartial_succ (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (i : Fin d) :
    kgChartPartial a G₀ i.succ = kgChartSpacePartial a G₀ i := by
  rw [kgChartPartial, Fin.cases_succ]

/-! ## The derivative along each coordinate -/

theorem hasDerivAt_kgChartField_zero
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (y : Fin (d + 1) → ℝ) :
    HasDerivAt (fun r : ℝ => kgChartField a G₀ (Function.update y 0 r))
      (kgChartTimePartial a G₀ y) (y 0) := by
  have hfun : (fun r : ℝ => kgChartField a G₀ (Function.update y 0 r))
      = fun r : ℝ => kgRealField a G₀ r (kgSpatial d y) := by
    funext r
    exact kgChartField_update_zero a G₀ y r
  rw [hfun, kgChartTimePartial]
  exact (differentiableAt_kgRealField_time a G₀ hN (kgSpatial d y) (y 0)).hasDerivAt

theorem hasDerivAt_kgChartField_succ
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (y : Fin (d + 1) → ℝ) (i : Fin d) :
    HasDerivAt (fun r : ℝ => kgChartField a G₀ (Function.update y i.succ r))
      (kgChartSpacePartial a G₀ i y) (y i.succ) := by
  set X : EuclideanSpace ℝ (Fin d) := kgSpatial d y with hX
  set V : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d i with hV
  have hfun : (fun r : ℝ => kgChartField a G₀ (Function.update y i.succ r))
      = fun r : ℝ => kgRealField a G₀ (y 0) (X + (r - y i.succ) • V) := by
    funext r
    exact kgChartField_update_succ a G₀ y i r
  have hbase : HasDerivAt (fun s : ℝ => kgRealField a G₀ (y 0) (X + s • V))
      (kgChartSpacePartial a G₀ i y) 0 := by
    rw [kgChartSpacePartial]
    exact (differentiableAt_kgRealField_dir a G₀ hN (y 0) X V 0).hasDerivAt
  have hbase' : HasDerivAt (fun s : ℝ => kgRealField a G₀ (y 0) (X + s • V))
      (kgChartSpacePartial a G₀ i y) (y i.succ - y i.succ) := by
    rw [sub_self]
    exact hbase
  have hcomp := HasDerivAt.comp_sub_const (f := fun s : ℝ =>
    kgRealField a G₀ (y 0) (X + s • V)) (y i.succ) (y i.succ) hbase'
  rw [hfun]
  exact hcomp

/-- **The chart field has all coordinate derivatives.** -/
theorem hasDerivAt_kgChartField_update
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (y : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    HasDerivAt (fun r : ℝ => kgChartField a G₀ (Function.update y j r))
      (kgChartPartial a G₀ j y) (y j) := by
  refine Fin.cases ?_ ?_ j
  · rw [kgChartPartial_zero]
    exact hasDerivAt_kgChartField_zero hN a G₀ y
  · intro i
    rw [kgChartPartial_succ]
    exact hasDerivAt_kgChartField_succ hN a G₀ y i

end GaloisForLFunctions.HTGeometry
