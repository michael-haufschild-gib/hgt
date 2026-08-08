import GaloisForLFunctions.HTGeometry.PowerSeriesJetCoeff
import GaloisForLFunctions.HTGeometry.PowerSeriesEndpointExpansion

/-!
# The endpoint sum runs over the genuine jets

In the endpoint expansion the variable slot `X` contributes nothing: its only nonzero coefficient
sits in degree one, while every endpoint index `N − q` with `q < R` is at least `R + 1 ≥ 3` once
`N ≥ 2R` and `R ≥ 2`.  So the endpoint sum reduces to the derivative slots, where the jet
coefficient formula turns each term into a coefficient of the underlying sequence weighted by a
descending factorial.

Reindexing the coefficient degree as `N = M + R` makes every endpoint index a *forward* shift
`M + (R − q + j)` of the base index `M`, which is what lets the one-sided fixed-shift asymptotic be
used throughout.
-/

open MvPolynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The `X` slot contributes nothing to an endpoint sum. -/
theorem endpoint_zero_slot_eq_zero (m R N : ℕ) (hR : 2 ≤ R) (hNR : 2 * R ≤ N)
    (F : PowerSeries ℂ) (P : MvPolynomial (Fin (m + 2)) ℂ) :
    (∑ q ∈ Finset.range R,
        PowerSeries.coeff q (aeval (formalJetsOver m F) (pderiv 0 P))
          * PowerSeries.coeff (N - q) (formalJetsOver m F 0)) = 0 := by
  refine Finset.sum_eq_zero fun q hq => ?_
  have hqR : q < R := Finset.mem_range.mp hq
  have hne : N - q ≠ 1 := by omega
  rw [coeff_formalJetsOver_zero_of_ne m F hne, mul_zero]

/-- **The endpoint sum runs over the derivative slots only.** -/
theorem endpoint_sum_eq_jet_sum (m R N : ℕ) (hR : 2 ≤ R) (hNR : 2 * R ≤ N)
    (F : PowerSeries ℂ) (P : MvPolynomial (Fin (m + 2)) ℂ) :
    (∑ j : Fin (m + 2), ∑ q ∈ Finset.range R,
        PowerSeries.coeff q (aeval (formalJetsOver m F) (pderiv j P))
          * PowerSeries.coeff (N - q) (formalJetsOver m F j))
      = ∑ j : Fin (m + 1), ∑ q ∈ Finset.range R,
          PowerSeries.coeff q (aeval (formalJetsOver m F) (pderiv j.succ P))
            * PowerSeries.coeff (N - q) (formalJetsOver m F j.succ) := by
  rw [Fin.sum_univ_succ, endpoint_zero_slot_eq_zero m R N hR hNR F P, zero_add]

/-- **The endpoint sum in terms of the coefficient sequence.** -/
theorem endpoint_sum_eq_coeff_sum (m R N : ℕ) (hR : 2 ≤ R) (hNR : 2 * R ≤ N)
    (a : ℕ → ℂ) (P : MvPolynomial (Fin (m + 2)) ℂ) :
    (∑ j : Fin (m + 2), ∑ q ∈ Finset.range R,
        PowerSeries.coeff q (aeval (formalJetsOver m (PowerSeries.mk a)) (pderiv j P))
          * PowerSeries.coeff (N - q) (formalJetsOver m (PowerSeries.mk a) j))
      = ∑ j : Fin (m + 1), ∑ q ∈ Finset.range R,
          PowerSeries.coeff q
              (aeval (formalJetsOver m (PowerSeries.mk a)) (pderiv j.succ P))
            * (a ((N - q) + (j : ℕ))
              * (((((N - q) + (j : ℕ)).descFactorial (j : ℕ) : ℕ)) : ℂ)) := by
  rw [endpoint_sum_eq_jet_sum m R N hR hNR _ P]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  rw [coeff_formalJetsOver_mk_succ]

/-- Reindexing the coefficient degree turns every endpoint index into a forward shift. -/
theorem endpoint_index_shift (M R q j : ℕ) (hq : q < R) :
    (M + R) - q + j = M + (R - q + j) := by
  omega

end

end GaloisForLFunctions.HTGeometry
