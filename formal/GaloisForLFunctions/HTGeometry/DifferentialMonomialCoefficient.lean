import GaloisForLFunctions.HTGeometry.TaylorDerivativeCoefficient

/-!
# The Taylor coefficient of a differential monomial

A differential monomial in a power series `f` is a finite product of iterated formal
derivatives `∏ₜ f^{(jₜ)}`.  Its `N`-th Taylor coefficient is a weighted convolution over the
antidiagonal: for every splitting of `N` into per-factor degrees `lₜ`, the contribution is the
product of the shifted coefficients `coeff (lₜ + jₜ) f` each weighted by the rising factorial
`(lₜ+1)⋯(lₜ+jₜ)` supplied by the `jₜ`-th derivative
(`coeff_prod_iterate_derivative`).

This is the arithmetic core of generic ADE coefficient extraction: expanding a differential
polynomial `P(z, f, f', …, f^{(m)})` on the generic series and reading off the `z^N`
coefficient produces exactly such convolution sums, one per monomial of `P`.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

variable {R : Type*} [CommSemiring R]

/-- **Differential-monomial coefficient.**  The `N`-th coefficient of a finite product of
iterated derivatives `∏ₜ f^{(jₜ)}` is the antidiagonal convolution of shifted coefficients,
each weighted by the rising factorial of its derivative order. -/
theorem coeff_prod_iterate_derivative {r : ℕ} (j : Fin r → ℕ) (f : R⟦X⟧) (N : ℕ) :
    coeff N (∏ t, (⇑(d⁄dX R))^[j t] f)
      = ∑ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N,
          ∏ t, coeff (l t + j t) f * ∏ i ∈ Finset.range (j t), ((l t + 1 + i : ℕ) : R) := by
  rw [PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.prod_congr rfl fun t _ => ?_
  exact coeff_iterate_derivative f (j t) (l t)

end GaloisForLFunctions

namespace GaloisForLFunctions

variable {R : Type*} [CommSemiring R]

/-- **Monomial with a `z`-power factor.**  Prepending `X^a` to a differential monomial shifts
its coefficient index by `a`: the `N`-th coefficient of `X^a · ∏ₜ f^{(jₜ)}` reads the
differential-monomial convolution at index `N - a`, and vanishes for `N < a`. -/
theorem coeff_X_pow_mul_prod_iterate_derivative {r : ℕ} (a : ℕ) (j : Fin r → ℕ) (f : R⟦X⟧)
    (N : ℕ) :
    coeff N (X ^ a * ∏ t, (⇑(d⁄dX R))^[j t] f)
      = if a ≤ N then
          ∑ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag (N - a),
            ∏ t, coeff (l t + j t) f * ∏ i ∈ Finset.range (j t), ((l t + 1 + i : ℕ) : R)
        else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_prod_iterate_derivative]
  · rfl

/-- **Source-sum constraint.**  Every convolution term contributing to the `N`-th coefficient
of a differential monomial `∏ₜ f^{(jₜ)}` reads original coefficients `a_{lₜ+jₜ}` whose indices
sum to `N + ∑ₜ jₜ` — the coefficient index plus the total derivative order.  This fixes the
source sum, the invariant on which the balanced-atom minimization operates. -/
theorem sum_source_index_of_mem_finsuppAntidiag {r N : ℕ} (j : Fin r → ℕ)
    {l : Fin r →₀ ℕ} (hl : l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N) :
    ∑ t, (l t + j t) = N + ∑ t, j t := by
  rw [Finset.sum_add_distrib]
  rw [Finset.mem_finsuppAntidiag] at hl
  rw [show (∑ t, l t) = ∑ t ∈ (Finset.univ : Finset (Fin r)), l t from rfl, hl.1]

end GaloisForLFunctions

namespace GaloisForLFunctions

variable {R : Type*} [CommSemiring R]

/-- **Support of a differential monomial.**  If the `N`-th coefficient of `∏ₜ f^{(jₜ)}` is
nonzero, then there is a choice of source exponents `kₜ`, each in the support of `f`, summing
to `N + ∑ₜ jₜ` (the coefficient index plus the total derivative order).  Thus a differential
monomial reads only source exponents of `f`, and their sum is pinned — the input to the
gap-series balanced-atom argument for differential monomials. -/
theorem exists_source_of_coeff_prod_iterate_derivative_ne_zero {r : ℕ} (j : Fin r → ℕ)
    (f : R⟦X⟧) (N : ℕ)
    (h : coeff N (∏ t, (⇑(d⁄dX R))^[j t] f) ≠ 0) :
    ∃ k : Fin r → ℕ, (∀ t, coeff (k t) f ≠ 0) ∧ ∑ t, k t = N + ∑ t, j t := by
  rw [coeff_prod_iterate_derivative] at h
  obtain ⟨l, hl, hlne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨fun t => l t + j t, fun t h0 => ?_, sum_source_index_of_mem_finsuppAntidiag j hl⟩
  exact hlne (Finset.prod_eq_zero (Finset.mem_univ t) (by rw [h0, zero_mul]))

end GaloisForLFunctions
