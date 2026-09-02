import GaloisForLFunctions.HTGeometry.CriticalBlockFieldNormalization

/-!
# Finite presentation of critical block normalizations

Every block normalization is module-finite over the marked observation chart. Since the chart is
Noetherian, this already gives the finite-presentation half of étaleness. Thus the remaining
purity obligation for a block cover is exactly formal étaleness, with no separate finite-type or
finite-presentation hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 400000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)]
variable (B : Set (criticalGeometricSheet K m n))

/-- A critical block normalization is finitely presented over the marked observation chart. -/
noncomputable instance criticalBlockNormalization_finitePresentation :
    Algebra.FinitePresentation (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) := by
  rw [← Algebra.FinitePresentation.of_finiteType]
  infer_instance

/-- For a critical block normalization, formal étaleness is the only remaining clause of
`Algebra.Etale`: finite presentation is unconditional. -/
theorem criticalBlockNormalization_etale_of_formallyEtale
    [Algebra.FormallyEtale (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B)] :
    Algebra.Etale (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) :=
  { formallyEtale := inferInstance
    finitePresentation := inferInstance }

end

end GaloisForLFunctions.HTGeometry
