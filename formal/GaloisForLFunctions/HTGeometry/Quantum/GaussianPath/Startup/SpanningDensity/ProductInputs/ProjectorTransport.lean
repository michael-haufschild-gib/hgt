import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.Intertwiner
import GaloisForLFunctions.HTGeometry.ContinuousCircuitMetricEntropyLaw
import GaloisForLFunctions.HTGeometry.DiagonalRotationCompiler

/-! # Intertwining one basis projector with its diagonal phase -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
noncomputable section

/-- Rank-one projector onto a computational basis vector. -/
def basisProjector {d : Type*} [DecidableEq d] (x : d) : Matrix d d ℂ :=
  diagonal fun i => if i=x then 1 else 0

/-- Evolution on one basis column differs from its diagonal phase by at
most elapsed time times its energy standard deviation, in operator norm. -/
theorem projector_residual {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (H : Matrix d d ℂ) (hH : IsSelfAdjoint H) (E : d→ℝ) (x : d) (hx : H x x=E x) (t : ℝ) :
    ‖unitaryEvolution H t*basisProjector x-basisProjector x*unitaryEvolution (diagonal (fun i => (E i:ℂ))) t‖ ≤
      |t| * Real.sqrt (∑ y ∈ Finset.univ.erase x, ‖H y x‖^2) := by
  letI : CStarAlgebra (Matrix d d ℂ) := {}
  let K : Matrix d d ℂ := diagonal fun i => (E i:ℂ)
  let P := basisProjector x
  have hK : IsSelfAdjoint K := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext i; simp
  let R := H*P-P*K
  have hr (y z : d) : R y z = if z=x ∧ y≠x then H y x else 0 := by
    by_cases hz : z=x
    · subst z
      by_cases hy : y=x
      · subst y; simp [R,P,basisProjector,K,mul_diagonal,hx]
      · simp [R,P,basisProjector,K,mul_diagonal,hy]
    · by_cases hy : y=x
      · subst y; simp [R,P,basisProjector,K,mul_diagonal,hz,Ne.symm hz]
      · by_cases h : y=z <;> simp [R,P,basisProjector,K,mul_diagonal,hz,hy,h]
  have hs : hsNorm R ^ 2 = ∑ y ∈ Finset.univ.erase x, ‖H y x‖^2 := by
    rw [hsNorm_sq]
    have hrow (y : d) : (∑ z, ‖R y z‖^2) = if y=x then 0 else ‖H y x‖^2 := by
      rw [Finset.sum_eq_single x]
      · by_cases h : y=x <;> simp [hr,h]
      · intro z _ hz; simp [hr,hz]
      · simp
    simp_rw [hrow]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    simp only [ite_true,add_zero]
    exact Finset.sum_congr rfl fun y hy => if_neg (Finset.ne_of_mem_erase hy)
  have hnorm : ‖R‖ ≤ Real.sqrt (∑ y ∈ Finset.univ.erase x, ‖H y x‖^2) := by
    rw [←hs,Real.sqrt_sq (hsNorm_nonneg _)]
    exact l2_opNorm_le_hsNorm _
  have he := Dephasing.hamiltonian_intertwiner_bound H K P hH hK t
  change ‖unitaryEvolution H t*P-P*unitaryEvolution K t‖ ≤ |t| *‖R‖ at he
  exact he.trans (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _))

#print axioms projector_residual
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
