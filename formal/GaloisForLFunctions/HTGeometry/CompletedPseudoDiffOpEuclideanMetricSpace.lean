import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpEuclideanTriangle

/-!
# Euclidean metric structure on projective completed lattices

The centered Cartan norm, with its proved separation and triangle laws, is packaged as a literal
metric structure.  It remains an explicit value rather than a global instance so it can coexist
with the coarser integral interleaving metric already available on the same carrier.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]
variable {r : ℕ}

@[reducible] noncomputable def differentialVariationalProjectiveEuclideanPseudoMetricSpace :
    PseudoMetricSpace (DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) where
  dist := differentialVariationalProjectiveEuclideanVertexDistance
  dist_self := differentialVariationalProjectiveEuclideanVertexDistance_self
  dist_comm := differentialVariationalProjectiveEuclideanVertexDistance_comm
  dist_triangle := differentialVariationalProjectiveEuclideanVertexDistance_triangle

@[reducible] noncomputable def differentialVariationalProjectiveEuclideanMetricSpace :
    MetricSpace (DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :=
  { differentialVariationalProjectiveEuclideanPseudoMetricSpace with
    eq_of_dist_eq_zero := by
      intro x y h
      exact (differentialVariationalProjectiveEuclideanVertexDistance_eq_zero_iff x y).1 h }

theorem differentialVariationalProjectiveEuclideanMetricSpace_dist
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    @dist _ differentialVariationalProjectiveEuclideanMetricSpace.toDist x y =
      differentialVariationalProjectiveEuclideanVertexDistance x y := rfl

end

end GaloisForLFunctions.HTGeometry.DiffOp
