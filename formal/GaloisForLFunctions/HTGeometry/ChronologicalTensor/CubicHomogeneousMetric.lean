import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicWeightedInterval
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Finite-dimensional metric structure of physical homogeneous observations

The proved physical capacity supplies a normed additive group and compatible
real normed-space structure. These are explicit definitions, avoiding a global
choice of norm on the ambient polynomial algebra. The finite coefficient
equivalence proves finite dimension, properness, and continuity of coordinates.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicHomogeneousGroupNorm (k : ℕ) : AddGroupNorm (cubicHomogeneousSpace k) where
  toAddGroupSeminorm := (cubicHomogeneousSeminorm k).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' P h := (cubicHomogeneousCapacity_definite k P).mp h

@[implicit_reducible]
def cubicHomogeneousNormedGroup (k : ℕ) :
    NormedAddCommGroup (cubicHomogeneousSpace k) :=
  (cubicHomogeneousGroupNorm k).toNormedAddCommGroup

@[implicit_reducible]
def cubicHomogeneousNormedSpace (k : ℕ) :
    letI := cubicHomogeneousNormedGroup k
    NormedSpace ℝ (cubicHomogeneousSpace k) := by
  letI := cubicHomogeneousNormedGroup k
  exact { (inferInstance : Module ℝ (cubicHomogeneousSpace k)) with
    norm_smul_le := fun r P => by
      change cubicHomogeneousCapacity k (r • P) ≤ ‖r‖*cubicHomogeneousCapacity k P
      exact cubicHomogeneousCapacity_smul_le k r P }

theorem cubicHomogeneousSpace_finiteDimensional (k : ℕ) :
    FiniteDimensional ℝ (cubicHomogeneousSpace k) :=
  FiniteDimensional.of_injective (cubicHomogeneousCoordinatesEquiv k).toLinearMap
    (cubicHomogeneousCoordinatesEquiv k).injective

theorem cubicHomogeneousSpace_proper (k : ℕ) :
    letI := cubicHomogeneousNormedGroup k
    ProperSpace (cubicHomogeneousSpace k) := by
  letI := cubicHomogeneousNormedGroup k
  letI := cubicHomogeneousNormedSpace k
  letI := cubicHomogeneousSpace_finiteDimensional k
  exact FiniteDimensional.proper ℝ (cubicHomogeneousSpace k)

theorem cubicHomogeneousCoordinates_continuous (k : ℕ) :
    letI := cubicHomogeneousNormedGroup k
    Continuous (cubicHomogeneousCoordinates k) := by
  letI := cubicHomogeneousNormedGroup k
  letI := cubicHomogeneousNormedSpace k
  letI := cubicHomogeneousSpace_finiteDimensional k
  exact (cubicHomogeneousCoordinatesEquiv k).toLinearMap.continuous_of_finiteDimensional

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
