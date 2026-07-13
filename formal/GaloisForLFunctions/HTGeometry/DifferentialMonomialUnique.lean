import GaloisForLFunctions.HTGeometry.DifferentialMonomialCoefficient

/-!
# Unique source representation makes a differential monomial coefficient nonzero

If exactly one antidiagonal splitting of `N` reads only nonzero source coefficients of `f`,
then the `N`-th coefficient of the differential monomial `∏ₜ f^{(jₜ)}` collapses to that single
term (`coeff_prod_iterate_derivative_of_unique`), a product of nonzero shifted coefficients and
nonzero rising-factorial weights, hence nonzero over a characteristic-zero field
(`coeff_prod_iterate_derivative_ne_zero_of_unique`).

This is the differential-monomial analogue of `coeff_pow_unique_rep`: for a lacunary series,
where the balanced source tuple is the unique representation of its sum, a differential monomial
retains a nonzero coefficient — the mechanism upgrading transcendence of a gap series to
differential transcendence.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

variable {R : Type*} [Field R] [CharZero R]

omit [CharZero R] in
/-- **Unique-source collapse.**  When one antidiagonal tuple `l₀` reads only nonzero source
coefficients and every other tuple hits a zero, the differential-monomial coefficient is the
single `l₀` term. -/
theorem coeff_prod_iterate_derivative_of_unique {r : ℕ} (j : Fin r → ℕ) (f : R⟦X⟧) (N : ℕ)
    (l₀ : Fin r →₀ ℕ) (hl₀ : l₀ ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N)
    (huniq : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N, l ≠ l₀ →
      ∃ t, coeff (l t + j t) f = 0) :
    coeff N (∏ t, (⇑(d⁄dX R))^[j t] f)
      = ∏ t, coeff (l₀ t + j t) f * ∏ i ∈ Finset.range (j t), ((l₀ t + 1 + i : ℕ) : R) := by
  rw [coeff_prod_iterate_derivative]
  refine Finset.sum_eq_single_of_mem l₀ hl₀ fun l hl hne => ?_
  obtain ⟨t, ht⟩ := huniq l hl hne
  exact Finset.prod_eq_zero (Finset.mem_univ t) (by rw [ht, zero_mul])

/-- **Unique-source nonvanishing.**  Under the same unique-source hypothesis, with every source
coefficient of the distinguished tuple nonzero, the differential-monomial coefficient is
nonzero. -/
theorem coeff_prod_iterate_derivative_ne_zero_of_unique {r : ℕ} (j : Fin r → ℕ) (f : R⟦X⟧)
    (N : ℕ) (l₀ : Fin r →₀ ℕ) (hl₀ : l₀ ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N)
    (hl₀ne : ∀ t, coeff (l₀ t + j t) f ≠ 0)
    (huniq : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N, l ≠ l₀ →
      ∃ t, coeff (l t + j t) f = 0) :
    coeff N (∏ t, (⇑(d⁄dX R))^[j t] f) ≠ 0 := by
  rw [coeff_prod_iterate_derivative_of_unique j f N l₀ hl₀ huniq]
  refine Finset.prod_ne_zero_iff.mpr fun t _ => mul_ne_zero (hl₀ne t) ?_
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact Nat.cast_ne_zero.mpr (by omega)

end GaloisForLFunctions
