import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingMetricSpace

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

/-- The integral projective interleaving metric is complete: every Cauchy filter contains a
singleton because distinct points have distance at least one. -/
noncomputable instance differentialVariationalProjectiveInterleavingCompleteSpace :
    CompleteSpace (DifferentialVariationalProjectiveBuildingCarrier K ι) where
  complete := by
    intro f hf
    have hf' := (Metric.cauchy_iff.mp hf)
    obtain ⟨s, hs, hdiam⟩ := hf'.2 1 zero_lt_one
    letI : f.NeBot := hf'.1
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hs
    refine ⟨x, le_trans ?_ (pure_le_nhds x)⟩
    rw [Filter.le_pure_iff]
    apply Filter.mem_of_superset hs
    intro y hy
    change y = x
    apply (differentialVariationalProjectiveInterleavingDistance_eq_zero_iff y x).1
    have hlt := hdiam y hy x hx
    rw [dist_eq_differentialVariationalProjectiveInterleavingDistance] at hlt
    have hnat :
        differentialVariationalProjectiveInterleavingDistance y x < 1 := by
      exact_mod_cast hlt
    omega

end

end GaloisForLFunctions.HTGeometry.DiffOp
