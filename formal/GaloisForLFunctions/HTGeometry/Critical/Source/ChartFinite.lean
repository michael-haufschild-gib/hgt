import GaloisForLFunctions.HTGeometry.Critical.Source.ChartObservationTower

/-!
# Finiteness of the critical source chart

The critical source chart is a principal open in affine space, hence is of finite type over the
ground field.  Since the observation chart is an intermediate ground-field algebra, finite type
descends to the source/observation chart tower.  The already proved integrality of that tower then
upgrades immediately to module finiteness.

This is the finite-module input needed for flatness and trace-retraction arguments on block
normalizations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)]

/-- The critical source chart is finitely generated over the observation chart. -/
noncomputable instance criticalSourceChartRing_finiteType :
    Algebra.FiniteType (criticalObservationChartRing K m n)
      (criticalSourceChartRing K m n) :=
  Algebra.FiniteType.of_restrictScalars_finiteType K
    (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)

/-- **The critical source chart is finite over the observation chart.** -/
noncomputable instance criticalSourceChartRing_finite :
    Module.Finite (criticalObservationChartRing K m n)
      (criticalSourceChartRing K m n) :=
  Algebra.IsIntegral.finite

end

end GaloisForLFunctions.HTGeometry
