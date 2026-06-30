/-
# `f = z²+c` is a degree-2 covering of the connected escape levels

For a parameter whose critical value `c = f(0)` never escapes (the connected case), the quadratic map
`f` restricts to an unbranched degree-2 covering `escapeLevel c (n+1) → escapeLevel c n`. This is the
covering structure underlying the `π₁ ≅ ℤ` of every escape level and the `f∗ = ·2` action that makes
the per-level winding even.

Built on Mathlib's `Polynomial.isCoveringMapOn_eval` (a polynomial is a covering on the complement of
its critical values); the only critical value of `z²+c` is `c`, which lies off the escape levels in the
connected case.
-/
import GaloisForLFunctions.Bottcher.BasinColimit
import GaloisForLFunctions.Bottcher.BasinBranching
import Mathlib.Analysis.Complex.CoveringMap

open Topology Polynomial

namespace Bottcher

/-- `quadratic c` is the evaluation of the polynomial `X² + C c`. -/
theorem quadratic_eq_eval (c : ℂ) : quadratic c = (quadraticPoly c).eval := by
  funext z; simp [quadratic, quadraticPoly]

/-- **#2.1 — `escapeLevel (n+1)` is the `f`-preimage of `escapeLevel n`.** -/
theorem escapeLevel_succ_eq_preimage (c : ℂ) (n : ℕ) :
    escapeLevel c (n + 1) = (quadratic c) ⁻¹' (escapeLevel c n) := by
  ext z
  simp only [escapeLevel, Set.mem_setOf_eq, Set.mem_preimage]
  rw [Function.iterate_succ_apply]

/-- The derivative of `X²+C c` evaluates to `2k`. -/
theorem deriv_eval_quadraticPoly (c k : ℂ) :
    (quadraticPoly c).derivative.eval k = 2 * k := by
  unfold quadraticPoly
  rw [derivative_add, derivative_X_pow, derivative_C, add_zero]
  simp

/-- The only critical value of `z²+c` is `c`: the image of the zero set of the derivative lands in
`{c}`. -/
theorem critical_values_quadratic (c : ℂ) :
    (quadraticPoly c).eval '' {k | (quadraticPoly c).derivative.eval k = 0} ⊆ {c} := by
  rintro w ⟨k, hk, rfl⟩
  simp only [Set.mem_setOf_eq, deriv_eval_quadraticPoly] at hk
  have hk0 : k = 0 := by
    rcases mul_eq_zero.mp hk with h | h
    · norm_num at h
    · exact h
  simp [Set.mem_singleton_iff, quadraticPoly, hk0]

/-- **#2.2 — `f = z²+c` is a degree-2 covering `escapeLevel (n+1) → escapeLevel n`.** Whenever the
critical value `c` does not lie in `escapeLevel c n` (the connected case, where the critical orbit is
bounded), `quadratic c` is a covering map over `escapeLevel c n`; its preimage is `escapeLevel c (n+1)`
(`escapeLevel_succ_eq_preimage`). -/
theorem isCoveringMapOn_quadratic_escapeLevel (c : ℂ) (n : ℕ) (hc : c ∉ escapeLevel c n) :
    IsCoveringMapOn (quadratic c) (escapeLevel c n) := by
  have hcov := (quadraticPoly c).isCoveringMapOn_eval
  rw [quadratic_eq_eval]
  refine hcov.mono ?_
  intro z hz
  rw [Set.mem_compl_iff]
  intro hzc
  exact hc ((critical_values_quadratic c hzc) ▸ hz)

end Bottcher
