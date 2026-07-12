import Mathlib

/-!
# Isolating a single summand at one coefficient index

A finite sum of power series is nonzero at index `N` as soon as exactly one summand is nonzero
there and all others vanish (`coeff_sum_ne_zero_of_unique`); consequently the sum is a nonzero
power series (`sum_ne_zero_of_unique_coeff`).

For a differential polynomial expanded as a sum of differential monomials, this is the
index-selection principle: to prove `P(f, f', …) ≠ 0` it suffices to exhibit one coefficient
index `N` at which a single monomial contributes and the rest cancel to zero — the exponent gap
of a lacunary series supplies such an `N`.
-/

open PowerSeries

namespace GaloisForLFunctions

/-- **Coefficient isolation.**  If one summand has a nonzero `N`-th coefficient and all others
vanish there, the finite sum has a nonzero `N`-th coefficient. -/
theorem coeff_sum_ne_zero_of_unique {R : Type*} [Semiring R] {ι : Type*} (s : Finset ι)
    (g : ι → R⟦X⟧) (N : ℕ) {μ₀ : ι} (hμ₀ : μ₀ ∈ s) (hne : coeff N (g μ₀) ≠ 0)
    (hother : ∀ μ ∈ s, μ ≠ μ₀ → coeff N (g μ) = 0) :
    coeff N (∑ μ ∈ s, g μ) ≠ 0 := by
  rw [map_sum, Finset.sum_eq_single_of_mem μ₀ hμ₀ hother]
  exact hne

/-- A finite sum of power series with an isolating coefficient index is a nonzero power
series. -/
theorem sum_ne_zero_of_unique_coeff {R : Type*} [Semiring R] {ι : Type*} (s : Finset ι)
    (g : ι → R⟦X⟧) (N : ℕ) {μ₀ : ι} (hμ₀ : μ₀ ∈ s) (hne : coeff N (g μ₀) ≠ 0)
    (hother : ∀ μ ∈ s, μ ≠ μ₀ → coeff N (g μ) = 0) :
    ∑ μ ∈ s, g μ ≠ 0 := by
  intro h
  exact coeff_sum_ne_zero_of_unique s g N hμ₀ hne hother (by rw [h, map_zero])

end GaloisForLFunctions
