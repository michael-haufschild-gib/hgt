import GaloisForLFunctions.HTGeometry.CriticalObservationComplexPoints
import GaloisForLFunctions.HTGeometry.TorusChartConnectedCover

/-!
# Connected finite covers of the critical observation chart

The exact complex-point homeomorphism transports every topological covering of the observation
chart to the standard torus-affine chart.  The existing torus fundamental-group classification then
produces a nontrivial cyclic character for every nontrivial connected finite cover.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {E : Type u} [TopologicalSpace E]

/-- Transport a map to the analytic torus-affine coordinates of the critical observation chart. -/
def criticalObservationAnalyticProjection
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)]
    (p : E → AlgSpec (criticalObservationChartRing ℂ m n)) :
    E → ComplexTorusAffineChart (n + m - 2) :=
  criticalObservationComplexPointHomeomorph m n ∘ p

/-- Coverings remain coverings after the exact analytic chart identification. -/
theorem criticalObservationAnalyticProjection_isCoveringMap
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)]
    {p : E → AlgSpec (criticalObservationChartRing ℂ m n)}
    (cov : IsCoveringMap p) :
    IsCoveringMap (criticalObservationAnalyticProjection m n p) :=
  cov.homeomorph_comp (criticalObservationComplexPointHomeomorph m n)

/-- **Every nontrivial connected finite cover of the critical observation chart supplies a
nontrivial finite cyclic torus character with an exponent pair not both divisible by its order.** -/
theorem criticalObservationConnectedFiniteCover_exists_nontrivial_cyclic_character
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)]
    (p : E → AlgSpec (criticalObservationChartRing ℂ m n))
    (cov : IsCoveringMap p)
    [PathConnectedSpace E]
    [Finite ((criticalObservationAnalyticProjection m n p) ⁻¹'
      {(1 : ComplexTorusAffineChart (n + m - 2))})]
    [Nontrivial ((criticalObservationAnalyticProjection m n p) ⁻¹'
      {(1 : ComplexTorusAffineChart (n + m - 2))})] :
    ∃ N : Subgroup
        ((criticalObservationAnalyticProjection_isCoveringMap m n cov).monodromyPerm
          (1 : ComplexTorusAffineChart (n + m - 2))).range,
      IsCoatom N ∧
        HasNontrivialCyclicTorusChartCharacter
          (criticalObservationAnalyticProjection m n p)
          (criticalObservationAnalyticProjection_isCoveringMap m n cov) N :=
  connectedFiniteTorusChartCover_exists_nontrivial_cyclic_character
    (criticalObservationAnalyticProjection m n p)
    (criticalObservationAnalyticProjection_isCoveringMap m n cov)

end

end GaloisForLFunctions.HTGeometry
