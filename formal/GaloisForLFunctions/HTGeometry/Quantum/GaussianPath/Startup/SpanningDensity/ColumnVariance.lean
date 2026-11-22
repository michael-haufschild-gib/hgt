import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.LocalVariance

/-! # Uniform computational-basis energy variance on a Pauli path -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

/-- Every computational-basis vector has energy variance at most 21
times the squared coefficient mass, independently of its diagonal energy. -/
theorem column_variance {n : ℕ} (u : PathShell n) (x : Fin (n+2)→Bool) :
    (∑ y ∈ Finset.univ.erase x, ‖pathHamiltonian u y x‖^2) ≤ 21*‖u‖^2 := by
  apply ProductInputs.local_column_variance u (fun l => finitePauliMatrix (pathWord l))
    (fun l => CStarRing.norm_of_mem_unitary (finitePauliMatrix_mem_unitary _)) _ _ (pathHamiltonian_eq_sum u)
  intro l v hi y x hv
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  rw [pathWord_none_of_not_incidentSite v l hi,boolPauliOptionEntry_none,if_neg hv]

#print axioms column_variance
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
