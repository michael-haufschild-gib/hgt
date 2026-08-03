import GaloisForLFunctions.HTGeometry.ClockBivariateSecondOrder
import GaloisForLFunctions.HTGeometry.ClockNullFrameEquivalence

/-!
# A twice differentiable characteristic solution is a clock probe

The null frame identifies a clock probe on two-dimensional Minkowski space with a solution of the
characteristic equation `∂ξ∂η u = K u`. That identification was already proved to be an equivalence;
what it needs as input is a solution which is twice continuously differentiable, because the chart
d'Alembertian reads second partial derivatives one direction at a time.

This file supplies the passage in that form: a bivariate function whose two first derivatives are
themselves continuously differentiable on an open planar set, and whose two mixed derivatives sum to
the potential term at one point, gives a clock probe at the corresponding event. No estimate and no
further regularity are used — the whole content is the second-order chart calculus of the previous
file fed into the null-frame equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- The clock field of a bivariate function: its value at the null coordinates of an event. -/
noncomputable def nullChartFun (u : ℝ → ℝ → ℝ) : (Fin (1 + 1) → ℝ) → ℝ :=
  fun y => chartFun u (nullFrame y)

theorem nullChartFun_apply (u : ℝ → ℝ → ℝ) (y : Fin (1 + 1) → ℝ) :
    nullChartFun u y = u (nullFrame y 0) (nullFrame y 1) := rfl

theorem nullChartFun_comp_invNullFrame (u : ℝ → ℝ → ℝ) :
    (fun y : Fin (1 + 1) → ℝ => nullChartFun u (invNullFrame y)) = chartFun u := by
  funext y
  show chartFun u (nullFrame (invNullFrame y)) = chartFun u y
  rw [nullFrame_invNullFrame]

/-- **A twice continuously differentiable characteristic solution is a clock probe.** -/
theorem solvesPotentialWaveAt_nullChartFun {u A B Aa Ab Ba Bb : ℝ → ℝ → ℝ} {Ω : Set (ℝ × ℝ)}
    {V : (Fin (1 + 1) → ℝ) → ℝ} (h : IsC1On u A B Ω) (hA : IsC1On A Aa Ab Ω)
    (hB : IsC1On B Ba Bb Ω) {x : Fin (1 + 1) → ℝ} (hx : nullFrame x ∈ chartBox Ω)
    (hchar : Ab (nullFrame x 0) (nullFrame x 1) + Ba (nullFrame x 0) (nullFrame x 1)
      = V x * u (nullFrame x 0) (nullFrame x 1) / 2) :
    SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V
      (nullChartFun u) x := by
  have hcomp := nullChartFun_comp_invNullFrame u
  have hu : ∀ z ∈ chartBox Ω,
      DifferentiableAt ℝ (fun y => nullChartFun u (invNullFrame y)) z := by
    intro z hz
    rw [hcomp]
    exact differentiableAt_chartFun h hz
  have hu2 : ∀ k : Fin (1 + 1), ∀ z ∈ chartBox Ω,
      DifferentiableAt ℝ (coordPartial k (fun y => nullChartFun u (invNullFrame y))) z := by
    intro k z hz
    rw [hcomp]
    exact differentiableAt_coordPartial_chartFun h hA hB k hz
  refine (solvesPotentialWaveAt_iff_characteristic (isOpen_chartBox h.isOpen) hx hu hu2).mpr ?_
  rw [hcomp, coordPartial_coordPartial_chartFun_zero_one h hA hx,
    coordPartial_coordPartial_chartFun_one_zero h hB hx]
  exact hchar

end GaloisForLFunctions.HTGeometry
