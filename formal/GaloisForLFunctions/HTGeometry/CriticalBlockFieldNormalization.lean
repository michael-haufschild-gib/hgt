import GaloisForLFunctions.HTGeometry.CriticalBlockFieldSourceDescent
import GaloisForLFunctions.HTGeometry.CriticalChartTowerFinite
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finite normalization of a critical block field

The observation chart is a Noetherian normal domain with the observation field as its fraction
field.  Every block-stabilizer fixed field is a finite separable intermediate extension.  The
integral closure of the chart in that field is therefore module-finite and has the block field as
its fraction field.  This is the canonical finite algebraic model of the block cover.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Fixed field attached to the setwise stabilizer of a set of critical sheets. -/
abbrev CriticalBlockFixedField (B : Set (criticalGeometricSheet K m n)) :=
  IntermediateField.fixedField (criticalBlockStabilizer K B)

/-- Normalization of the observation chart in a block-stabilizer fixed field. -/
abbrev CriticalBlockNormalization (B : Set (criticalGeometricSheet K m n)) :=
  integralClosure (criticalObservationChartRing K m n) (CriticalBlockFixedField K B)

/-- A block fixed field is finite-dimensional over the observation field. -/
noncomputable instance criticalBlockFixedField_finiteDimensional
    (B : Set (criticalGeometricSheet K m n)) :
    FiniteDimensional (criticalObservationField K m n) (CriticalBlockFixedField K B) := by
  letI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K Fact.out Fact.out
  infer_instance

/-- **Finite normalization.**  The canonical block model is module-finite over the actual
observation chart. -/
noncomputable instance criticalBlockNormalization_finite
    (B : Set (criticalGeometricSheet K m n)) :
    Module.Finite (criticalObservationChartRing K m n) (CriticalBlockNormalization K B) := by
  letI : Algebra.IsSeparable (criticalObservationField K m n) (CriticalBlockFixedField K B) :=
    inferInstance
  exact IsIntegralClosure.finite
    (criticalObservationChartRing K m n)
    (criticalObservationField K m n)
    (CriticalBlockFixedField K B)
    (CriticalBlockNormalization K B)

/-- The function field of the finite normalization is exactly the block fixed field. -/
noncomputable instance criticalBlockNormalization_isFractionRing
    (B : Set (criticalGeometricSheet K m n)) :
    IsFractionRing (CriticalBlockNormalization K B) (CriticalBlockFixedField K B) :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (criticalObservationChartRing K m n)
    (criticalObservationField K m n)
    (CriticalBlockFixedField K B)
    (CriticalBlockNormalization K B)

/-- The finite block normalization is Noetherian. -/
instance criticalBlockNormalization_isNoetherianRing
    (B : Set (criticalGeometricSheet K m n)) :
    IsNoetherianRing (CriticalBlockNormalization K B) :=
  IsNoetherianRing.of_finite (criticalObservationChartRing K m n)
    (CriticalBlockNormalization K B)

end

end GaloisForLFunctions.HTGeometry
