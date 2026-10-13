import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic

/-! Finite-node power differences detect exactly the power sums constant on the nodes. -/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

def finitePowerDifferenceMatrix (r n : ℕ) (x : Fin (r + 1) → ℝ) :
    Matrix (Fin r) (Fin n) ℝ :=
  fun i j => x i.succ ^ ((j : ℕ) + 1) - x 0 ^ ((j : ℕ) + 1)

theorem finitePowerDifferenceMatrix_mulVec_eq_zero_iff
    (r n : ℕ) (x : Fin (r + 1) → ℝ) (c : Fin n → ℝ) :
    (finitePowerDifferenceMatrix r n x).mulVec c = 0 ↔
      ∀ i, (∑ j : Fin n, c j * x i ^ ((j : ℕ) + 1)) =
        ∑ j : Fin n, c j * x 0 ^ ((j : ℕ) + 1) := by
  constructor
  · intro h i
    refine Fin.cases rfl (fun k => ?_) i
    have hk := congrFun h k
    change (∑ j : Fin n, (x k.succ ^ ((j : ℕ) + 1) -
      x 0 ^ ((j : ℕ) + 1)) * c j) = 0 at hk
    simp only [sub_mul, Finset.sum_sub_distrib] at hk
    simpa only [mul_comm] using sub_eq_zero.mp hk
  · intro h
    funext i
    change (∑ j : Fin n, (x i.succ ^ ((j : ℕ) + 1) -
      x 0 ^ ((j : ℕ) + 1)) * c j) = 0
    simp only [sub_mul, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    simpa only [mul_comm] using h i.succ

end GaloisForLFunctions.HTGeometry
