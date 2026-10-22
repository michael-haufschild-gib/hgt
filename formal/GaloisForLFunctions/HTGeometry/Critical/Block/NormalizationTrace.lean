import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationChart
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartFinite
import Mathlib.RingTheory.Trace.Basic

/-!
# Normalized trace from the critical source chart to a block normalization

For a monodromy block containing the canonical source sheet, its fixed field embeds in the actual
critical source field. The normalized field trace along this finite extension sends source-chart
elements to elements integral over the observation chart: ordinary trace preserves integrality,
and the inverse degree is already a ground-field scalar in the observation chart. Thus normalized
trace canonically lands in the block normalization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet K m n)}
variable (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
  (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)

/-- Inverse source-over-block degree, regarded as a scalar of the observation chart. -/
noncomputable def criticalBlockTraceDenominator :
    criticalObservationChartRing K m n := by
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
  exact algebraMap K (criticalObservationChartRing K m n)
    ((Module.finrank (CriticalBlockFixedField K B) (criticalSourceField K m n) : K)⁻¹)

/-- Normalized source-over-block field trace, restricted to the actual source chart. -/
noncomputable def criticalBlockNormalizedTraceToField :
    criticalSourceChartRing K m n →ₗ[criticalObservationChartRing K m n]
      CriticalBlockFixedField K B := by
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
  exact criticalBlockTraceDenominator K hB hmem •
    ((Algebra.trace (CriticalBlockFixedField K B)
      (criticalSourceField K m n)).restrictScalars
        (criticalObservationChartRing K m n)).comp
          (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
            (criticalSourceChartRing K m n) (criticalSourceField K m n)).toLinearMap

/-- Normalized trace of a source-chart element is integral over the observation chart. -/
theorem criticalBlockNormalizedTraceToField_isIntegral
    (s : criticalSourceChartRing K m n) :
    IsIntegral (criticalObservationChartRing K m n)
      (criticalBlockNormalizedTraceToField K hB hmem s) := by
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
  have hs : IsIntegral (criticalObservationChartRing K m n)
      (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) s) :=
    (Algebra.IsIntegral.isIntegral s).map
      (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n) (criticalSourceField K m n))
  have ht : IsIntegral (criticalObservationChartRing K m n)
      (Algebra.trace (CriticalBlockFixedField K B) (criticalSourceField K m n)
        (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) s)) :=
    Algebra.isIntegral_trace hs
  rw [criticalBlockNormalizedTraceToField, LinearMap.smul_apply, LinearMap.comp_apply]
  change IsIntegral (criticalObservationChartRing K m n)
    (criticalBlockTraceDenominator K hB hmem •
      Algebra.trace (CriticalBlockFixedField K B) (criticalSourceField K m n)
        (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) s))
  rw [Algebra.smul_def]
  exact isIntegral_algebraMap.mul ht

/-- Normalized trace, with codomain restricted to the finite block normalization. -/
noncomputable def criticalBlockNormalizedTraceToNormalization :
    criticalSourceChartRing K m n →ₗ[criticalObservationChartRing K m n]
      CriticalBlockNormalization K B :=
  LinearMap.codRestrict (CriticalBlockNormalization K B).toSubmodule
    (criticalBlockNormalizedTraceToField K hB hmem)
    (fun s => criticalBlockNormalizedTraceToField_isIntegral K hB hmem s)

end

end GaloisForLFunctions.HTGeometry
