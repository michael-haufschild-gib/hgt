import GaloisForLFunctions.TaylorDerivativeCoefficient

/-!
# The iterated-derivative weight is a falling factorial

The rising-factorial weight `(k+1)(k+2)⋯(k+j)` of the iterated-derivative coefficient is the
falling factorial of the source index: `∏_{i<j}(k+1+i) = (k+j)⁽ʲ⁾` in descending form
(`prod_range_succ_add_eq_descFactorial`).  Hence the `k`-th coefficient of the `j`-th formal
derivative is the source coefficient times `descFactorial (k+j) j`
(`coeff_iterate_derivative_eq_descFactorial`).

Read at a uniform source `s`, a differential monomial with derivative orders `{jₜ}` carries the
weight `∏ₜ descFactorial s jₜ` — a product of falling factorials of `s`.  This is the
leading-symbol form of the extraction weight: the polynomial in `s` whose non-degeneracy
separates same-degree monomials of a differential polynomial.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

/-- The rising-factorial weight equals the falling factorial of the source index. -/
theorem prod_range_succ_add_eq_descFactorial (k j : ℕ) :
    ∏ i ∈ Finset.range j, (k + 1 + i) = Nat.descFactorial (k + j) j := by
  rw [Nat.descFactorial_eq_prod_range, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  omega

variable {R : Type*} [CommSemiring R]

/-- **Falling-factorial coefficient form.**  The `k`-th coefficient of the `j`-th formal
derivative of `f` is the `(k+j)`-th coefficient of `f` times the falling factorial
`descFactorial (k+j) j`. -/
theorem coeff_iterate_derivative_eq_descFactorial (f : R⟦X⟧) (j k : ℕ) :
    coeff k ((⇑(d⁄dX R))^[j] f)
      = coeff (k + j) f * (Nat.descFactorial (k + j) j : R) := by
  rw [coeff_iterate_derivative, ← Nat.cast_prod, prod_range_succ_add_eq_descFactorial]

end GaloisForLFunctions
