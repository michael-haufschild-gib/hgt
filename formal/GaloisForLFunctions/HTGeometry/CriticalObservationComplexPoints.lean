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

/-- The actual observation-chart complex-point space is second countable through its explicit
finite-dimensional torus-affine model. -/
noncomputable instance criticalObservationAlgSpec_secondCountableTopology
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    SecondCountableTopology (AlgSpec (criticalObservationChartRing ℂ m n)) := by
  letI : SecondCountableTopology (Units ℂ) :=
    (unitsHomeomorphNeZero (G₀ := ℂ)).secondCountableTopology
  exact (criticalObservationComplexPointHomeomorph m n).secondCountableTopology

/-- The actual observation-chart complex-point space has the compact-coherence instance needed to
read compact-preimage finiteness as properness. -/
instance criticalObservationAlgSpec_compactlyCoherentSpace
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    CompactlyCoherentSpace (AlgSpec (criticalObservationChartRing ℂ m n)) := by
  infer_instance

end

end GaloisForLFunctions.HTGeometry
