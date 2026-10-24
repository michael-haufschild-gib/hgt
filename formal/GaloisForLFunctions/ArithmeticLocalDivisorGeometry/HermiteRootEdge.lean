import GaloisForLFunctions.HTGeometry.HermiteRealRoots
import GaloisForLFunctions.HTGeometry.HermitePerturbationRealRoots
import Mathlib.Analysis.Polynomial.Order

/-!
# The outermost Hermite zero

The Gaussian half-line Rolle theorem makes the largest zero strictly increase with degree.
Every lower Hermite polynomial is positive at that zero. These exact signs locate the sharp
stationary-point boundary for inverse heat; the power bound supplies its universal upper scale.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

private theorem hermiteRoots_nonempty (n : ℕ) : (gaussianDerivZeros (n + 1)).Nonempty := by
  apply Finset.card_pos.mp
  exact lt_of_lt_of_le (Nat.succ_pos n) (card_roots_toFinset_hermite (n + 1))

/-- Largest zero of the probabilists' Hermite polynomial of degree `n + 1`. -/
def hermiteEdge (n : ℕ) : ℝ := (gaussianDerivZeros (n + 1)).max' (hermiteRoots_nonempty n)

theorem hermiteEdge_isRoot (n : ℕ) : (hermiteReal (n + 1)).eval (hermiteEdge n) = 0 := by
  exact (gaussianDeriv_eq_zero_iff _ _).mp
    ((mem_gaussianDerivZeros _ _).mp (Finset.max'_mem _ (hermiteRoots_nonempty n)))

theorem le_hermiteEdge_of_root (n : ℕ) {x : ℝ}
    (hx : (hermiteReal (n + 1)).eval x = 0) : x ≤ hermiteEdge n := by
  apply Finset.le_max'
  exact (mem_gaussianDerivZeros _ _).mpr ((gaussianDeriv_eq_zero_iff _ _).mpr hx)

/-- The outer Rolle zero lies strictly beyond the previous largest Hermite zero. -/
theorem hermiteEdge_strictMono : StrictMono hermiteEdge := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨x, hx, hz⟩ := exists_hasDerivAt_eq_zero_Ioi (hasDerivAt_gaussianDeriv (n + 1))
    ((gaussianDeriv_eq_zero_iff _ _).mpr (hermiteEdge_isRoot n))
    (tendsto_gaussianDeriv_atTop (n + 1))
  exact hx.trans_le (le_hermiteEdge_of_root (n + 1) ((gaussianDeriv_eq_zero_iff _ _).mp hz))

@[simp] theorem hermiteEdge_zero : hermiteEdge 0 = 0 := by
  simpa only [Nat.zero_add, eval_hermiteReal_one] using hermiteEdge_isRoot 0

theorem hermiteEdge_nonneg (n : ℕ) : 0 ≤ hermiteEdge n := by
  simpa only [hermiteEdge_zero] using hermiteEdge_strictMono.monotone (Nat.zero_le n)

theorem hermiteEdge_pos {n : ℕ} (hn : 0 < n) : 0 < hermiteEdge n := by
  simpa only [hermiteEdge_zero] using hermiteEdge_strictMono hn

/-- All Hermite weights through degree `n + 1` are positive beyond the outermost zero. -/
theorem hermite_eval_pos_of_edge_lt {n j : ℕ} {x : ℝ}
    (hj : j ≤ n + 1) (hx : hermiteEdge n < x) : 0 < (hermiteReal j).eval x := by
  cases j with
  | zero => simp only [eval_hermiteReal_zero]; norm_num
  | succ j =>
    apply zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    · intro y hy
      exact (le_hermiteEdge_of_root j hy).trans_lt
        ((hermiteEdge_strictMono.monotone (by omega)).trans_lt hx)
    · rw [((hermite_monic (j + 1)).map (Int.castRingHom ℝ)).leadingCoeff]
      norm_num

/-- At the outermost zero, every lower Hermite degree has strictly positive weight. -/
theorem hermite_eval_pos_at_edge {n j : ℕ} (hj : j ≤ n) :
    0 < (hermiteReal j).eval (hermiteEdge n) := by
  cases j with
  | zero => simp only [eval_hermiteReal_zero]; norm_num
  | succ j =>
    exact hermite_eval_pos_of_edge_lt (n := j) (le_refl _) (hermiteEdge_strictMono (by omega))

/-- The existing power lower bound excludes a Hermite zero at or beyond `2 sqrt(n+1)`. -/
theorem hermiteEdge_lt_two_sqrt (n : ℕ) : hermiteEdge n < 2 * Real.sqrt (n + 1 : ℕ) := by
  by_contra hn
  have hx := le_of_not_gt hn
  have h := (pow_half_le_aeval_hermite (n := n + 1) hx (n + 1) (le_refl _)).1
  rw [aeval_hermite_eq, show realHermite (n + 1) = hermiteReal (n + 1) from rfl,
    hermiteEdge_isRoot] at h
  have hs : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have he : 0 < hermiteEdge n := (by positivity : 0 < 2 * Real.sqrt (n + 1 : ℕ)).trans_le hx
  exact (not_le_of_gt (pow_pos (by positivity : 0 < hermiteEdge n / 2) _)) h

/-- The next Hermite polynomial is negative at the outermost critical point. -/
theorem hermite_eval_succ_edge_neg (n : ℕ) :
    (hermiteReal (n + 2)).eval (hermiteEdge n) < 0 := by
  rw [eval_hermiteReal_add_two, hermiteEdge_isRoot, mul_zero, zero_sub]
  exact neg_neg_of_pos (mul_pos (by positivity)
    (hermite_eval_pos_at_edge (n := n) (le_refl _)))

/-- The outermost critical point is a strict quadratic local minimum. -/
theorem hermite_second_derivative_edge_pos (n : ℕ) :
    0 < (derivative (derivative (hermiteReal (n + 2)))).eval (hermiteEdge n) := by
  rw [show n + 2 = (n + 1) + 1 by omega, derivative_hermiteReal_succ,
    derivative_C_mul, derivative_hermiteReal_succ, eval_mul, eval_C, eval_mul, eval_C]
  exact mul_pos (by positivity) (mul_pos (by positivity)
    (hermite_eval_pos_at_edge (n := n) (le_refl _)))

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
