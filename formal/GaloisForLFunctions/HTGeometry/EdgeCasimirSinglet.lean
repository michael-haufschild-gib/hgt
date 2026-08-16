import GaloisForLFunctions.HTGeometry.RotationQuadraticCasimir
import GaloisForLFunctions.HTGeometry.FixedEdgeSingletDefect

/-!
# The full edge Casimir preserves the singlet sector

Summing the square of the edge commutator over all nine orientations of an edge gives an operator
commuting with the collective generator at either endpoint, and trivially with the generators away
from the edge.  The full edge Casimir of a family of edges therefore preserves the sitewise singlet
sector.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The square sum of one edge over all nine orientations. -/
def edgeOrientationCasimir (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (i j : I) :
    Matrix (FiniteAllReplicaOperatorIndex I R) (FiniteAllReplicaOperatorIndex I R) ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    fixedEdgeCommutatorMatrix I R i j a b * fixedEdgeCommutatorMatrix I R i j a b

theorem commute_edgeOrientationCasimir_left {i j : I} (hij : i ≠ j) (c : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R i c * edgeOrientationCasimir I R i j =
      edgeOrientationCasimir I R i j * finiteAllReplicaCollectiveCommutatorMatrix I R i c := by
  classical
  rw [edgeOrientationCasimir, Finset.sum_comm, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact commute_sum_sq_of_rotation _ (fun a => fixedEdgeCommutatorMatrix I R i j a b) c
    (fun a => collectiveCommutator_fixedEdgeCommutator_bracket_left hij c a b)

theorem commute_edgeOrientationCasimir_right {i j : I} (hij : i ≠ j) (c : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R j c * edgeOrientationCasimir I R i j =
      edgeOrientationCasimir I R i j * finiteAllReplicaCollectiveCommutatorMatrix I R j c := by
  classical
  rw [edgeOrientationCasimir, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact commute_sum_sq_of_rotation _ (fun b => fixedEdgeCommutatorMatrix I R i j a b) c
    (fun b => collectiveCommutator_fixedEdgeCommutator_bracket_right hij c a b)

theorem commute_edgeOrientationCasimir_notMem {i j v : I} (hvi : v ≠ i) (hvj : v ≠ j)
    (c : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R v c * edgeOrientationCasimir I R i j =
      edgeOrientationCasimir I R i j * finiteAllReplicaCollectiveCommutatorMatrix I R v c := by
  classical
  rw [edgeOrientationCasimir, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hc := collectiveCommutator_fixedEdgeCommutator_comm_of_notMem (I := I) (R := R) hvi hvj c a b
  rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, hc, ← Matrix.mul_assoc]

/-- **The edge Casimir of one edge preserves the sitewise singlet sector.** -/
theorem edgeOrientationCasimir_mem_singlet {i j : I} (hij : i ≠ j)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    (edgeOrientationCasimir I R i j).toEuclideanLin x ∈
      finiteAllReplicaCollectiveSingletSubspace I R := by
  classical
  refine mem_singlet_iff.mpr fun v c => ?_
  have hcomm : finiteAllReplicaCollectiveCommutatorMatrix I R v c * edgeOrientationCasimir I R i j =
      edgeOrientationCasimir I R i j * finiteAllReplicaCollectiveCommutatorMatrix I R v c := by
    by_cases hvi : v = i
    · subst hvi
      exact commute_edgeOrientationCasimir_left hij c
    · by_cases hvj : v = j
      · subst hvj
        exact commute_edgeOrientationCasimir_right hij c
      · exact commute_edgeOrientationCasimir_notMem hvi hvj c
  rw [← toEuclideanLin_mul_apply, hcomm, toEuclideanLin_mul_apply,
    (mem_singlet_iff.mp hx) v c, map_zero]


theorem fixedEdgeCommutatorMatrix_conjTranspose {i j : I} (hij : i ≠ j) (a b : Fin 3) :
    (fixedEdgeCommutatorMatrix I R i j a b)ᴴ = fixedEdgeCommutatorMatrix I R i j a b :=
  matrixCommutatorRepresentation_conjTranspose (fixedEdgeCollectivePauli_isHermitian hij a b)

theorem adjoint_fixedEdgeCommutator {i j : I} (hij : i ≠ j) (a b : Fin 3) :
    LinearMap.adjoint (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin =
      (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    fixedEdgeCommutatorMatrix_conjTranspose hij]

/-- **The edge Casimir is the sum of the squared norms of the nine edge images.** -/
theorem inner_edgeOrientationCasimir_self {i j : I} (hij : i ≠ j)
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    @inner ℂ _ _ x ((edgeOrientationCasimir I R i j).toEuclideanLin x) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        ((‖(fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x‖ : ℂ)) ^ 2 := by
  classical
  rw [edgeOrientationCasimir]
  simp only [map_sum, LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [toEuclideanLin_mul_apply]
  rw [← adjoint_fixedEdgeCommutator hij a b, LinearMap.adjoint_inner_right,
    adjoint_fixedEdgeCommutator hij a b]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _

/-- **On the singlet sector the edge Casimir kernel is the joint edge kernel.** -/
theorem edgeOrientationCasimir_apply_eq_zero_iff {i j : I} (hij : i ≠ j)
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    (edgeOrientationCasimir I R i j).toEuclideanLin x = 0 ↔
      ∀ a b : Fin 3, (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x = 0 := by
  classical
  constructor
  · intro hzero a b
    have hinner : @inner ℂ _ _ x ((edgeOrientationCasimir I R i j).toEuclideanLin x) = 0 := by
      rw [hzero, inner_zero_right]
    rw [inner_edgeOrientationCasimir_self hij] at hinner
    have hreal : (∑ a : Fin 3, ∑ b : Fin 3,
        ‖(fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x‖ ^ 2) = 0 := by
      have hcast : ((∑ a : Fin 3, ∑ b : Fin 3,
          ‖(fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x‖ ^ 2 : ℝ) : ℂ) = 0 := by
        push_cast
        exact hinner
      exact_mod_cast hcast
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a' _ => Finset.sum_nonneg fun b' _ => sq_nonneg _)).mp hreal a (Finset.mem_univ a)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b' _ => sq_nonneg _)).mp hrow b (Finset.mem_univ b)
    have hnorm := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
    exact norm_eq_zero.mp hnorm
  · intro hall
    rw [edgeOrientationCasimir]
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [toEuclideanLin_mul_apply, hall a b, map_zero]

end GaloisForLFunctions.HTGeometry
