import GaloisForLFunctions.HTGeometry.ProjectiveIncidenceProjection
import GaloisForLFunctions.HTGeometry.ClassicalStratifiedParametricAvoidance

/-!
# From projective incidence dimension to finite smooth strata

This module isolates the second and final classical algebraic-geometric input in the carrier
genericity argument.  For a finite polynomial matrix, its nonzero null vectors form a closed
incidence subvariety over projective coefficient space.  The projection to packet space is proper;
therefore it is algebraic and cannot have dimension greater than the incidence variety.  A finite
Whitney stratification then gives smooth real strata, and complex codimension `c` becomes real
codimension `2 * c`.

The structure below states that standard theorem only for the completely general finite expanded
polynomial matrix appearing in the project.  It assumes the Krull bound on every standard affine
projective chart.  It does not assume any Nevanlinna, carrier, density, or transversality
conclusion.  The project-specific work—identifying the projected incidence with the literal rank
defect and proving every chart bound—is Lean-checked in this and preceding modules.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- Exact classical proper-projection plus Whitney-stratification interface.

The bound says that every affine chart of the projective null-vector incidence has complex
dimension at most the packet dimension minus `c`.  The conclusion is a finite smooth
stratification of its projected bad set with real codimension at least `2 * c`. -/
structure ClassicalComplexProjectiveIncidenceGeometry : Prop where
  finite_stratification_of_chart_krull_bounds :
    ∀ {row κ : Type}
      [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
      (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) (c : ℕ),
      (∀ j : κ × Fin (q + 1),
        ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
            (c : WithBot ℕ∞) ≤
          (Fintype.card row * n : ℕ)) →
      FiniteRegularStratification
        (projectiveChartIncidenceProjection q n z exponent) (2 * c)

/-- **Projected expanded-evaluation codimension law.**  The exact global incidence-ring theorem,
proper projective projection, and finite Whitney stratification give real codimension twice the
formal complex excess

`card(row) - card(coefficients) - q + 1`.

All deductions specific to the expanded differential-evaluation matrix are proved here in Lean;
`classicalInput` contains only the general algebraic-geometric theorem above. -/
theorem expandedDifferentialEvaluationRankDefect_finiteRegularStratification
    (classicalInput : ClassicalComplexProjectiveIncidenceGeometry)
    {row κ : Type}
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row) :
    FiniteRegularStratification
      (expandedDifferentialEvaluationRankDefect q n z exponent)
      (2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1)) := by
  let c := Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1
  rw [expandedDifferentialEvaluationRankDefect_eq_projectiveChartIncidenceProjection]
  exact classicalInput.finite_stratification_of_chart_krull_bounds
    q n z exponent c (fun j => by
      exact projectiveChartGlobalIncidenceRing_evaluationCodimension
        q n z hz j exponent hexponent hrows)

end

end GaloisForLFunctions.HTGeometry
