import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy

/-!
# Finite positive-block exclusion of consecutive common roots

Global positive moment forms are unnecessary for the basic Sturm obstruction.  One positive finite
Hankel block supplies the three-term recurrence and strict positivity of its Jacobi edges.  A
common root of two consecutive monic orthogonal polynomials would therefore descend degree by
degree to a root of the constant polynomial.
-/

open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Finite no-common-root law.**  Positivity only through degree `N-1` excludes a common root of
`P_n` and `P_(n+1)` whenever `n+1 ≤ N`; no infinite moment-form premise is used. -/
theorem monicOrtho_succ_no_common_root_below
    {N n : ℕ} (h : PositiveMomentFormBelow s N) (hnN : n + 1 ≤ N) {x : ℝ}
    (hn : (monicOrtho s n).eval x = 0)
    (hn1 : (monicOrtho s (n + 1)).eval x = 0) : False := by
  induction n with
  | zero =>
      rw [monicOrtho_zero, Polynomial.eval_one] at hn
      exact one_ne_zero hn
  | succ n ih =>
      have hrec := X_mul_monicOrtho_below h (n := n + 1) hnN
      have hev := congrArg (Polynomial.eval x) hrec
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
        Polynomial.eval_smul, smul_eq_mul] at hev
      rw [hn, hn1] at hev
      simp only [mul_zero, zero_add] at hev
      have hbeta : 0 < monicOrthoBeta s (n + 1) :=
        monicOrthoBeta_pos_below h (by omega) (by omega)
      have hprev : (monicOrtho s n).eval x = 0 := by
        have hprod : monicOrthoBeta s (n + 1) *
            (monicOrtho s n).eval x = 0 := by
          simpa only [Nat.succ_sub_one] using hev.symm
        exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hbeta)
      exact ih (by omega) hprev hn

end HTGeometry
