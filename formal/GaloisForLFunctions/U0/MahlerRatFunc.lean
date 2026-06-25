/-
# The Mahler obstruction at the field level `ℂ(z) = RatFunc ℂ`

`MahlerPolynomial.no_coprime_mahler_rational` is stated for a coprime pair of polynomials. This file
packages it for the function field `ℂ(z) = RatFunc ℂ` via the canonical coprime numerator/denominator
of a rational function: a `g ∈ ℂ(z)` satisfying the Mahler equation `g(z²+c) = g(z)²` (in
cross-multiplied numerator/denominator form) must be **constant** for `c ≠ 0`.

This is the field-level obstruction consumed by the `n ≥ 2` norm-descent: if `φ_c` is algebraic over
`ℂ(z)` of degree `n ≥ 2`, its norm `N(φ_c) ∈ ℂ(z)` satisfies `N(φ_c)(z²+c) = N(φ_c)(z)²` (the Mahler
equation descends along the multiplicative norm), so `ratfunc_mahler_const` forces `N(φ_c)` constant.
-/
import GaloisForLFunctions.U0.MahlerPolynomial
import Mathlib.FieldTheory.RatFunc.Basic

open Polynomial

namespace MahlerPolynomial

/-- **Field-level Mahler obstruction over `ℂ(z)` (PROVED).** If `g ∈ ℂ(z)` has numerator/denominator
satisfying `num(z²+c)·denom(z)² = num(z)²·denom(z²+c)` — the cleared-denominator form of `g(z²+c) =
g(z)²` — then for `c ≠ 0` both `num g` and `denom g` are constant, i.e. `g` is a constant. Immediate from
`no_coprime_mahler_rational` applied to the canonical coprime pair `(num g, denom g)`. -/
theorem ratfunc_mahler_const {c : ℂ} (hc : c ≠ 0) {g : RatFunc ℂ}
    (heq : (RatFunc.num g).comp (X ^ 2 + C c) * (RatFunc.denom g) ^ 2
      = (RatFunc.num g) ^ 2 * (RatFunc.denom g).comp (X ^ 2 + C c)) :
    (RatFunc.num g).natDegree = 0 ∧ (RatFunc.denom g).natDegree = 0 := by
  by_contra hcon
  have hnc : 0 < (RatFunc.num g).natDegree ∨ 0 < (RatFunc.denom g).natDegree := by
    by_contra h2
    push_neg at h2
    exact hcon ⟨Nat.le_zero.mp h2.1, Nat.le_zero.mp h2.2⟩
  have hg : g ≠ 0 := by
    rintro rfl
    simp only [RatFunc.num_zero, RatFunc.denom_zero, natDegree_zero, natDegree_one,
      lt_self_iff_false, or_self] at hnc
  exact no_coprime_mahler_rational hc (RatFunc.isCoprime_num_denom g)
    (RatFunc.num_ne_zero hg) (RatFunc.denom_ne_zero g) heq hnc

end MahlerPolynomial
