import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationTraceCoercion

/-!
# Evaluation formulas for the critical block normalized trace

The source-over-block algebra structure depends on a concrete block and its canonical-sheet
membership proof. This module isolates the resulting typeclass reductions behind opaque
evaluation lemmas: extension degree, trace on an embedded block element, positivity of the degree,
and the observation-chart value of the inverse-degree scalar.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 5000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet K m n)}
variable (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
  (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)

/-- Degree of the actual critical source field over the fixed field of the block stabilizer. -/
noncomputable def criticalBlockExtensionDegree : ℕ := by
  letI : Algebra (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    (blockFieldToSource K hB hmem).toAlgebra
  letI : IsScalarTower (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (blockFieldToSource K hB hmem).commutes x |>.symm
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K Fact.out Fact.out
  letI : FiniteDimensional (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    FiniteDimensional.right (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n)
  exact Module.finrank (CriticalBlockFixedField K B) (criticalSourceField K m n)

/-- Field trace for the concrete source-over-block field inclusion. -/
noncomputable def criticalBlockFieldTraceValue (x : criticalSourceField K m n) :
    CriticalBlockFixedField K B := by
  letI : Algebra (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    (blockFieldToSource K hB hmem).toAlgebra
  exact Algebra.trace (CriticalBlockFixedField K B) (criticalSourceField K m n) x

/-- Pointwise evaluation of normalized trace on the source chart. -/
theorem criticalBlockNormalizedTraceToField_apply (s : criticalSourceChartRing K m n) :
    criticalBlockNormalizedTraceToField K hB hmem s =
      criticalBlockTraceDenominator K hB hmem •
        criticalBlockFieldTraceValue K hB hmem
          (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) s) := by
  letI : Algebra (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    (blockFieldToSource K hB hmem).toAlgebra
  letI : IsScalarTower (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (blockFieldToSource K hB hmem).commutes x |>.symm
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K Fact.out Fact.out
  letI : FiniteDimensional (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    FiniteDimensional.right (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n)
  letI : IsScalarTower (criticalObservationChartRing K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (criticalObservationChartRing K m n)
        (criticalObservationField K m n) (criticalSourceField K m n)]
      rw [IsScalarTower.algebraMap_apply (criticalObservationChartRing K m n)
        (criticalObservationField K m n) (CriticalBlockFixedField K B)]
      exact (blockFieldToSource K hB hmem).commutes _ |>.symm
  rw [criticalBlockNormalizedTraceToField, LinearMap.smul_apply, LinearMap.comp_apply]
  change criticalBlockTraceDenominator K hB hmem •
      Algebra.trace (CriticalBlockFixedField K B) (criticalSourceField K m n)
        (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) s) = _
  rfl

/-- Trace of an embedded block-normalization element is degree times that element. -/
theorem criticalBlockFieldTraceValue_blockNormalizationToSource
    (b : CriticalBlockNormalization K B) :
    criticalBlockFieldTraceValue K hB hmem (blockNormalizationToSource K hB hmem b) =
      criticalBlockExtensionDegree K hB hmem • b.1 := by
  letI : Algebra (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    (blockFieldToSource K hB hmem).toAlgebra
  letI : IsScalarTower (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (blockFieldToSource K hB hmem).commutes x |>.symm
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K Fact.out Fact.out
  letI : FiniteDimensional (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    FiniteDimensional.right (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n)
  change Algebra.trace (CriticalBlockFixedField K B) (criticalSourceField K m n)
      (algebraMap (CriticalBlockFixedField K B) (criticalSourceField K m n) b.1) =
    Module.finrank (CriticalBlockFixedField K B) (criticalSourceField K m n) • b.1
  exact Algebra.trace_algebraMap b.1

/-- Source-over-block extension degree is positive. -/
theorem criticalBlockExtensionDegree_pos : 0 < criticalBlockExtensionDegree K hB hmem := by
  letI : Algebra (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    (blockFieldToSource K hB hmem).toAlgebra
  letI : IsScalarTower (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (blockFieldToSource K hB hmem).commutes x |>.symm
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K Fact.out Fact.out
  letI : FiniteDimensional (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    FiniteDimensional.right (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n)
  rw [criticalBlockExtensionDegree]
  exact Module.finrank_pos

/-- The trace denominator maps to the inverse extension degree in the block field. -/
theorem algebraMap_criticalBlockTraceDenominator :
    algebraMap (criticalObservationChartRing K m n) (CriticalBlockFixedField K B)
        (criticalBlockTraceDenominator K hB hmem) =
      algebraMap K (CriticalBlockFixedField K B)
        ((criticalBlockExtensionDegree K hB hmem : K)⁻¹) := by
  letI : Algebra (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    (blockFieldToSource K hB hmem).toAlgebra
  letI : IsScalarTower (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (blockFieldToSource K hB hmem).commutes x |>.symm
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K Fact.out Fact.out
  letI : FiniteDimensional (CriticalBlockFixedField K B) (criticalSourceField K m n) :=
    FiniteDimensional.right (criticalObservationField K m n)
      (CriticalBlockFixedField K B) (criticalSourceField K m n)
  letI : IsScalarTower K (criticalObservationChartRing K m n)
      (CriticalBlockFixedField K B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K (criticalObservationField K m n)
        (CriticalBlockFixedField K B)]
      rw [IsScalarTower.algebraMap_apply K (criticalObservationChartRing K m n)
        (criticalObservationField K m n)]
      rw [← IsScalarTower.algebraMap_apply (criticalObservationChartRing K m n)
        (criticalObservationField K m n) (CriticalBlockFixedField K B)]
  rw [criticalBlockTraceDenominator, criticalBlockExtensionDegree]
  exact (IsScalarTower.algebraMap_apply K (criticalObservationChartRing K m n)
    (CriticalBlockFixedField K B) _).symm

end

end GaloisForLFunctions.HTGeometry
