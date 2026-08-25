import GaloisForLFunctions.HTGeometry.CriticalObservationTorusChartEquiv
import GaloisForLFunctions.HTGeometry.TorusChartComplexPoints

/-!
# Complex points of the critical observation chart

The algebraic observation-chart identification and the complex-points homeomorphism for the
standard torus-affine chart combine into the exact analytic model used by topological monodromy.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The complex points of the critical observation chart are `(ℂˣ)² × ℂ^(n+m-2)`.** -/
noncomputable def criticalObservationComplexPointHomeomorph
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    AlgSpec (criticalObservationChartRing ℂ m n) ≃ₜ
      ComplexTorusAffineChart (n + m - 2) :=
  (AlgSpec.homeomorphOfAlgEquiv
    (criticalObservationChartTorusAlgEquiv ℂ m n)).symm.trans
      (torusChartComplexPointHomeomorph (n + m - 2))

end

end GaloisForLFunctions.HTGeometry
