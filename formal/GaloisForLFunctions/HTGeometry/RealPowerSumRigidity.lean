import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Real.Basic

/-! A finite sum of distinct positive powers vanishes everywhere only with zero coefficients. -/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

theorem real_power_sum_succ_eq_zero_iff (n : ℕ) (c : Fin n → ℝ) :
    (∀ x : ℝ, (∑ i : Fin n, c i * x ^ ((i : ℕ) + 1)) = 0) ↔ c = 0 := by
  classical
  constructor
  · intro h
    let p : Polynomial ℝ := ∑ i : Fin n, Polynomial.monomial ((i : ℕ) + 1) (c i)
    have hp : p = 0 := by
      apply Polynomial.funext
      intro x
      simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial] using h x
    funext i
    have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff ((i : ℕ) + 1)) hp
    simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj] using hcoeff
  · rintro rfl x
    simp

end GaloisForLFunctions.HTGeometry
