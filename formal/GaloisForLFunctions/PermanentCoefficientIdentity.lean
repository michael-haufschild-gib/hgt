import GaloisForLFunctions.DifferentialMonomialCoefficient
import GaloisForLFunctions.SuperIncreasingSourceUnique
import GaloisForLFunctions.PermanentDistinctSymbol

/-!
# The distinct-index coefficient is a permanent

At `r` distinct source scales `bnat Mᵢ` the coefficient of a differential monomial `∏ₜ f^{(μₜ)}`
of a tail-supported superlacunary series is a **permanent** over those scales.  Unlike the balanced
index (all sources equal, a single surviving antidiagonal point → the weight polynomial), the
distinct index has `r!` surviving antidiagonal points — one per assignment `π` of the `r` factors to
the `r` scales — and they sum to `(∏ᵢ coeff (bnat Mᵢ) f) · permSymbol`.

The `coeff_prod_iterate_derivative_of_subset` lemma isolates the surviving set; `multiset_source_unique`
identifies it as exactly the permutation orbit of the balanced assignment.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

variable {R : Type*} [CommSemiring R]

/-- **Coefficient supported on a surviving subset.**  If every antidiagonal index outside a subset
`T` kills the differential-monomial product (some factor reads a zero coefficient of `f`), then the
`N`-th coefficient is the sum over `T` alone.  Generalises `coeff_prod_iterate_derivative_of_unique`
from one surviving index to the full permutation orbit. -/
theorem coeff_prod_iterate_derivative_of_subset {r : ℕ} (j : Fin r → ℕ) (f : R⟦X⟧) (N : ℕ)
    (T : Finset (Fin r →₀ ℕ)) (hT : T ⊆ (Finset.univ : Finset (Fin r)).finsuppAntidiag N)
    (hvanish : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N, l ∉ T →
      ∃ t, coeff (l t + j t) f = 0) :
    coeff N (∏ t, (⇑(d⁄dX R))^[j t] f)
      = ∑ l ∈ T, ∏ t, coeff (l t + j t) f * ∏ i ∈ Finset.range (j t), ((l t + 1 + i : ℕ) : R) := by
  rw [coeff_prod_iterate_derivative]
  symm
  apply Finset.sum_subset hT
  intro l hl hnotT
  obtain ⟨t, ht⟩ := hvanish l hl hnotT
  exact Finset.prod_eq_zero (Finset.mem_univ t) (by rw [ht, zero_mul])

end GaloisForLFunctions
