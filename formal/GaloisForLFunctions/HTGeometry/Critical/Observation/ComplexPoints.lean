import GaloisForLFunctions.HTGeometry.Critical.Observation.TorusChartEquiv
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

/-- The first analytic torus coordinate is the marked raw observation coordinate. -/
theorem criticalObservationComplexPointHomeomorph_first_val
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)]
    (chi : AlgSpec (criticalObservationChartRing ℂ m n)) :
    ((criticalObservationComplexPointHomeomorph m n chi).1 : ℂ) =
      chi (algebraMap (criticalObservationRing ℂ m n)
        (criticalObservationChartRing ℂ m n)
        (MvPolynomial.X (Sum.inl (⟨0, Fact.out⟩ : Fin n)))) := by
  rw [criticalObservationComplexPointHomeomorph,
    Homeomorph.trans_apply, torusChartComplexPointHomeomorph_first_val]
  change chi ((criticalObservationChartTorusAlgEquiv ℂ m n).symm
    (algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) ℂ)
      (TorusChart ℂ (n + m - 2)) (MvPolynomial.X 0))) = _
  congr 1
  apply (criticalObservationChartTorusAlgEquiv ℂ m n).injective
  rw [(criticalObservationChartTorusAlgEquiv ℂ m n).apply_symm_apply]
  exact (criticalObservationChartTorusEquiv_inl_zero ℂ m n).symm

/-- The second analytic torus coordinate is the marked reciprocal observation coordinate. -/
theorem criticalObservationComplexPointHomeomorph_second_val
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)]
    (chi : AlgSpec (criticalObservationChartRing ℂ m n)) :
    ((criticalObservationComplexPointHomeomorph m n chi).2.1 : ℂ) =
      chi (algebraMap (criticalObservationRing ℂ m n)
        (criticalObservationChartRing ℂ m n)
        (MvPolynomial.X (Sum.inr (⟨0, Fact.out⟩ : Fin m)))) := by
  rw [criticalObservationComplexPointHomeomorph,
    Homeomorph.trans_apply, torusChartComplexPointHomeomorph_second_val]
  change chi ((criticalObservationChartTorusAlgEquiv ℂ m n).symm
    (algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) ℂ)
      (TorusChart ℂ (n + m - 2)) (MvPolynomial.X 1))) = _
  congr 1
  apply (criticalObservationChartTorusAlgEquiv ℂ m n).injective
  rw [(criticalObservationChartTorusAlgEquiv ℂ m n).apply_symm_apply]
  exact (criticalObservationChartTorusEquiv_inr_zero ℂ m n).symm

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
