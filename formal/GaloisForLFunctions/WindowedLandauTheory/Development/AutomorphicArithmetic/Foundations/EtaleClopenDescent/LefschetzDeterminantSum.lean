import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AboveDimensionTrace
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Evaluating the local determinant gives the alternating sum of its
exterior-degree coefficients. -/

open Matrix Polynomial

namespace GlobalTheory.PD

/-- The local coefficients in the holomorphic Lefschetz formula
sum to the determinant of the cotangent action with scalar parameter. -/
theorem sum_lefschetzCoefficients {k : Type} [Field k] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) k) (y : k) :
    (∑ p ∈ Finset.range (d + 1), (-y) ^ p *
      ((1 + (X : Polynomial k) • M.map C).det.coeff p / (1 - M).det)) =
      (1 - y • M).det / (1 - M).det := by
  let P : Polynomial k := (1 + (X : Polynomial k) • M.map C).det
  have hdeg : P.natDegree < d + 1 := by
    apply Nat.lt_succ_of_le
    exact natDegree_le_iff_coeff_eq_zero.mpr fun a ha =>
      coeff_det_one_add_X_smul_eq_zero_of_dim_lt ha M
  have heval : P.eval (-y) = (1 - y • M).det := by
    dsimp only [P]
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp only [eval_add, eval_mul, eval_X, eval_C, eval_one, eval_zero] <;> ring
  rw [← heval, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end GlobalTheory.PD
