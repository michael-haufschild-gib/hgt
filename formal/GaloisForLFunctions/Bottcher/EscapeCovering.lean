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

/-! ## The deck transformation of `f` is `z ↦ -z`

`f(z)=z²+c` satisfies `f(-z)=f(z)`, and `-z` escapes exactly when `z` does, so `z ↦ -z` is the
nontrivial deck transformation of the degree-2 covering `f : escapeLevel c (n+1) → escapeLevel c n`.
This is the concrete generator of the deck group `ℤ/2` — the explicit handle on the covering's
2-sheeted structure (no abstract deck-group theory needed). -/

/-- `f(z)=z²+c` is even: `f(-z)=f(z)`. -/
theorem quadratic_neg (c z : ℂ) : quadratic c (-z) = quadratic c z := by
  simp only [quadratic]; ring

/-- `-z` escapes at level `n` exactly when `z` does. -/
theorem neg_mem_escapeLevel (c : ℂ) (n : ℕ) (z : ℂ) :
    -z ∈ escapeLevel c n ↔ z ∈ escapeLevel c n := by
  cases n with
  | zero => simp [escapeLevel, escapeOpen]
  | succ m =>
    simp only [escapeLevel, Set.mem_setOf_eq, Function.iterate_succ_apply, quadratic_neg]

/-- **The deck transformation** `z ↦ -z` of `escapeLevel c n`, an involutive homeomorphism. -/
def negHomeoEscape (c : ℂ) (n : ℕ) : escapeLevel c n ≃ₜ escapeLevel c n where
  toFun z := ⟨-(z : ℂ), (neg_mem_escapeLevel c n z).mpr z.2⟩
  invFun z := ⟨-(z : ℂ), (neg_mem_escapeLevel c n z).mpr z.2⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The deck transformation is genuinely a deck transformation of `f`: `f ∘ (z ↦ -z) = f`. -/
theorem quadratic_comp_neg (c : ℂ) (n : ℕ) (z : escapeLevel c (n + 1)) :
    quadratic c ((negHomeoEscape c (n + 1) z : ℂ)) = quadratic c (z : ℂ) := by
  show quadratic c (-(z : ℂ)) = quadratic c (z : ℂ)
  exact quadratic_neg c z

end Bottcher
