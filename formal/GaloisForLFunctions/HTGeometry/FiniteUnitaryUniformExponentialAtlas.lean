import GaloisForLFunctions.HTGeometry.CompactConnectedGroupUniformPower
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPathConnected
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

/-!
# A uniform finite exponential atlas for finite unitary groups

The logarithm chart on the radius-two ball around the identity is local.  A symmetric radius-one
subneighbourhood has a fixed finite power equal to `U(d)`, by compact connectedness.  Consequently
every finite unitary matrix is a product of exactly one fixed number of self-adjoint exponentials.
-/

open Set Topology Metric Matrix
open scoped Pointwise Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A symmetric radius-one identity neighbourhood in a finite unitary group. -/
def finiteUnitaryLogNeighborhood
    (ι : Type*) [Fintype ι] [DecidableEq ι] : Set (Matrix.unitaryGroup ι ℂ) :=
  Metric.ball 1 1 ∩ (Metric.ball 1 1)⁻¹

/-- The finite-unitary logarithm neighbourhood is open. -/
theorem finiteUnitaryLogNeighborhood_isOpen
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsOpen (finiteUnitaryLogNeighborhood ι) := by
  exact isOpen_ball.inter isOpen_ball.inv

/-- The identity lies in the finite-unitary logarithm neighbourhood. -/
theorem finiteUnitaryLogNeighborhood_one_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (1 : Matrix.unitaryGroup ι ℂ) ∈ finiteUnitaryLogNeighborhood ι := by
  simp [finiteUnitaryLogNeighborhood]

/-- The finite-unitary logarithm neighbourhood is closed under inversion as a set. -/
theorem finiteUnitaryLogNeighborhood_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (finiteUnitaryLogNeighborhood ι)⁻¹ = finiteUnitaryLogNeighborhood ι := by
  simp [finiteUnitaryLogNeighborhood, inter_comm]

/-- A fixed finite number of principal-logarithm exponentials reaches every finite unitary
matrix.  The number depends only on the matrix dimension, never on the target matrix. -/
theorem exists_finiteUnitary_uniform_expUnitary_prod
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ N : ℕ, ∀ U : Matrix.unitaryGroup ι ℂ,
      ∃ K : Fin N → selfAdjoint (Matrix ι ι ℂ),
        (List.ofFn fun i => selfAdjoint.expUnitary (K i)).prod = U := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  obtain ⟨N, hN⟩ := exists_pow_eq_univ_of_compact_connected
    (finiteUnitaryLogNeighborhood_isOpen (ι := ι))
    (finiteUnitaryLogNeighborhood_one_mem (ι := ι))
    (finiteUnitaryLogNeighborhood_inv (ι := ι))
  refine ⟨N, fun U => ?_⟩
  have hU : U ∈ (finiteUnitaryLogNeighborhood ι) ^ N := by
    rw [hN]
    exact Set.mem_univ U
  obtain ⟨f, hprod⟩ := Set.mem_pow.mp hU
  refine ⟨fun i => Unitary.argSelfAdjoint (f i), ?_⟩
  have hlog (i : Fin N) : selfAdjoint.expUnitary (Unitary.argSelfAdjoint (f i)) =
      (f i : Matrix.unitaryGroup ι ℂ) := by
    apply expUnitary_argSelfAdjoint
    have hnorm : ‖((f i : Matrix.unitaryGroup ι ℂ) - 1 : Matrix ι ι ℂ)‖ < 1 := by
      simpa only [finiteUnitaryLogNeighborhood, Set.mem_inter_iff, Metric.mem_ball,
        Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm] using (f i).2.1
    exact hnorm.trans (by norm_num)
  simp_rw [hlog]
  exact hprod

end

end GaloisForLFunctions.HTGeometry
