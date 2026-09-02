import Mathlib.Topology.MetricSpace.Isometry
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingMetric

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

/-- Real-valued metric induced by the exact natural-number projective interleaving distance. -/
noncomputable instance differentialVariationalProjectiveInterleavingPseudoMetricSpace :
    PseudoMetricSpace (DifferentialVariationalProjectiveBuildingCarrier K ι) where
  dist x y := differentialVariationalProjectiveInterleavingDistance x y
  dist_self x := by
    simp
  dist_comm x y := by
    exact_mod_cast differentialVariationalProjectiveInterleavingDistance_comm x y
  dist_triangle x y z := by
    exact_mod_cast differentialVariationalProjectiveInterleavingDistance_triangle x y z

noncomputable instance differentialVariationalProjectiveInterleavingMetricSpace :
    MetricSpace (DifferentialVariationalProjectiveBuildingCarrier K ι) where
  eq_of_dist_eq_zero := by
    intro x y h
    apply (differentialVariationalProjectiveInterleavingDistance_eq_zero_iff x y).1
    change (differentialVariationalProjectiveInterleavingDistance x y : ℝ) = 0 at h
    exact_mod_cast h

@[simp] theorem dist_eq_differentialVariationalProjectiveInterleavingDistance
    (x y : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    dist x y = differentialVariationalProjectiveInterleavingDistance x y := rfl

end

end GaloisForLFunctions.HTGeometry.DiffOp
