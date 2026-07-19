import GaloisForLFunctions.HTGeometry.NevDenominatorFactor
import GaloisForLFunctions.HTGeometry.EntryComplexLimit

/-!
# The truncated entries as polynomials

Each truncated entry is a polynomial expression in its argument, and its closed form (link 152) is an
identity between two such polynomials holding at every real point.  Since `ℝ` is infinite the
polynomials are equal, so the closed form transfers to complex arguments by `aeval`.

Done here for `D`; the other three entries follow the same three steps with their own closed forms.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The truncated `D` entry as a polynomial. -/
noncomputable def nevDpoly (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  C (momentInner s (monicOrtho s 0) (monicOrtho s 0)) * X *
    ∑ k ∈ Finset.range (n + 1),
      C ((monicOrtho s k).eval 0 / momentInner s (monicOrtho s k) (monicOrtho s k)) *
        monicOrtho s k

theorem nevDpoly_eval (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (nevDpoly s n).eval x = nevDreal s n x := by
  rw [nevDpoly, nevDreal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_finsetSum]
  rw [Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-- **The closed form as a polynomial identity.** -/
theorem nevDpoly_eq (h : PositiveMomentForm s) (n : ℕ) :
    nevDpoly s n
      = C (momentInner s (monicOrtho s 0) (monicOrtho s 0) /
            momentInner s (monicOrtho s n) (monicOrtho s n)) *
          (C ((monicOrtho s n).eval 0) * monicOrtho s (n + 1)
            - C ((monicOrtho s (n + 1)).eval 0) * monicOrtho s n) := by
  refine Polynomial.funext fun x => ?_
  rw [nevDpoly_eval, nevDreal_closed h n x]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]

/-- **The closed form at a complex argument.** -/
theorem nevDpoly_aeval (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    Polynomial.aeval z (nevDpoly s n)
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) /
            momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
          ((((monicOrtho s n).eval 0 : ℝ) : ℂ) * monicOrthoC s (n + 1) z
            - (((monicOrtho s (n + 1)).eval 0 : ℝ) : ℂ) * monicOrthoC s n z) := by
  rw [nevDpoly_eq h n]
  simp only [map_mul, map_sub, Polynomial.aeval_C, monicOrthoC, Complex.coe_algebraMap]

/-- The polynomial and the complex truncation agree. -/
theorem nevDtruncC_eq_aeval (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    nevDtruncC s n z = Polynomial.aeval z (nevDpoly s n) := by
  rw [nevDtruncC, nevDpoly, bilinearPartialSum]
  simp only [map_mul, map_sum, Polynomial.aeval_C, Polynomial.aeval_X, Complex.coe_algebraMap,
    monicOrthoC]
  rw [Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  push_cast
  ring

/-- **The complex closed form for the truncated `D` entry.** -/
theorem nevDtruncC_closed (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    nevDtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) /
            momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
          ((((monicOrtho s n).eval 0 : ℝ) : ℂ) * monicOrthoC s (n + 1) z
            - (((monicOrtho s (n + 1)).eval 0 : ℝ) : ℂ) * monicOrthoC s n z) := by
  rw [nevDtruncC_eq_aeval, nevDpoly_aeval h n z]

end HTGeometry
