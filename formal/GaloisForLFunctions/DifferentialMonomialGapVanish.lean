import GaloisForLFunctions.DifferentialMonomialCoefficient
import GaloisForLFunctions.GapOvershoot

/-!
# Source-sum too large: a differential monomial coefficient vanishes

A differential monomial of degree `r` reading source exponents in the tail of a monotone gap
sequence has zero coefficient at any index `N` whose source sum `N + ∑ₜ jₜ` lies strictly
between `r·bnat M` and `bnat (M+1)` (`coeff_prod_iterate_derivative_eq_zero_of_gt`): the
overshoot bound forces every source index `≤ M`, capping the achievable source sum at `r·bnat M`,
below the required value.

At the balanced index of a top-degree differential monomial this vanishes every lower-degree
(and higher-order same-degree) monomial — the degree-separation step of non-homogeneous
hypertranscendence.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

/-- **Source-sum overshoot vanishing.**  If the required source sum exceeds `r·bnat M` yet stays
below `bnat (M+1)`, the differential-monomial coefficient is zero. -/
theorem coeff_prod_iterate_derivative_eq_zero_of_gt {bnat : ℕ → ℕ} (hmono : Monotone bnat)
    {r : ℕ} (j : Fin r → ℕ) {f : ℂ⟦X⟧}
    (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    {N M : ℕ} (hlt : r * bnat M < N + ∑ t, j t) (hub : N + ∑ t, j t < bnat (M + 1)) :
    coeff N (∏ t, (⇑(d⁄dX ℂ))^[j t] f) = 0 := by
  by_contra hcon
  obtain ⟨k, hkne, hksum⟩ := exists_source_of_coeff_prod_iterate_derivative_ne_zero j f N hcon
  choose nt hnt using fun t => hsupp (k t) (hkne t)
  have hsum_nat : ∑ t, bnat (nt t) = N + ∑ t, j t := by
    rw [← hksum]; exact Finset.sum_congr rfl (fun t _ => (hnt t).symm)
  have hall := all_le_of_sum_bnat_lt hmono hsum_nat hub
  have hle : ∑ t, bnat (nt t) ≤ r * bnat M := by
    calc ∑ t, bnat (nt t) ≤ ∑ _t : Fin r, bnat M := Finset.sum_le_sum fun t _ => hmono (hall t)
      _ = r * bnat M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hsum_nat] at hle
  omega

end GaloisForLFunctions
