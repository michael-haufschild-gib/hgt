import GaloisForLFunctions.HTGeometry.GaussQuadratureNodes
import GaloisForLFunctions.HTGeometry.SecondKindMomentPolynomials

/-!
# Consecutive orthogonal polynomials share no root

The Wronskian identity `Q_{n+1} R_n − Q_n R_{n+1} = −hₙ/h₀` has a nonzero constant on the right.  A
common root of `Qₙ` and `Q_{n+1}` would make the left side vanish there, so no such root exists.

Consequently the Gauss node sets of consecutive levels are disjoint: the quadrature nodes always
move.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **No common root.**  `Qₙ` and `Q_{n+1}` cannot vanish at the same point. -/
theorem monicOrtho_succ_no_common_root (h : PositiveMomentForm s) (n : ℕ) {x : ℝ}
    (hn : (monicOrtho s n).eval x = 0) (hn1 : (monicOrtho s (n + 1)).eval x = 0) : False := by
  have hw := momentWronskian_eq h n
  have hev := congrArg (Polynomial.eval x) hw
  rw [momentWronskian, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hn, hn1,
    zero_mul, zero_mul, sub_zero, Polynomial.eval_C] at hev
  have hpos : (0 : ℝ) < momentInner s (monicOrtho s n) (monicOrtho s n) /
      momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    div_pos (monicOrtho_inner_self_pos h n) (monicOrtho_inner_self_pos h 0)
  linarith

/-- **The Gauss nodes of consecutive levels are disjoint.** -/
theorem gaussNodes_disjoint_succ (h : PositiveMomentForm s) (n : ℕ) :
    Disjoint (gaussNodes s n) (gaussNodes s (n + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha ha1
  exact monicOrtho_succ_no_common_root h (n + 1)
    ((mem_gaussNodes_iff n a).mp ha) ((mem_gaussNodes_iff (n + 1) a).mp ha1)

end HTGeometry
