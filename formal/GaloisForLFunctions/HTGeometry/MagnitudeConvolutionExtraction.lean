import GaloisForLFunctions.HTGeometry.DifferentialMonomialGapValue

/-!
# Full-support convolution extraction of a differential monomial coefficient

For a full-support power series `f = ∑ aₖ Xᵏ`, the `N`-th coefficient of a differential monomial
`∏ₜ f^{(jₜ)}` is the antidiagonal convolution

`coeff N (∏ₜ (d/dX)^[jₜ] f) = ∑_{∑ lₜ = N} ∏ₜ a_{lₜ + jₜ} · descFactorial(lₜ + jₜ, jₜ)`,

reindexed to source tuples `kₜ = lₜ + jₜ` with `∑ kₜ = N + ∑ jₜ`.  Each derivative factor
`(d/dX)^[j] f` has `coeff m = a_{m+j} · descFactorial(m+j, j)` (falling-factorial weight), and
`coeff_prod` expands the product over the finite antidiagonal.  Unlike the support-gap case, every
source tuple contributes; isolating the surviving atom is a magnitude-domination argument, not a
support separation.
-/

open PowerSeries Finset
open scoped Nat

namespace GaloisForLFunctions

/-- Falling-factorial coefficient of an iterated formal derivative:
`coeff m ((d/dX)^[j] f) = a_{m+j} · descFactorial(m+j, j)`. -/
theorem coeff_iterate_deriv (f : ℂ⟦X⟧) (j : ℕ) (m : ℕ) :
    (coeff m) ((⇑(d⁄dX ℂ))^[j] f)
      = (coeff (m + j)) f * ((m + j).descFactorial j : ℂ) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih (m + 1),
      show m + 1 + j = m + (j + 1) by omega, mul_assoc]
    congr 1
    rw [Nat.descFactorial_succ, show m + (j + 1) - j = m + 1 by omega]
    push_cast; ring

/-- **Full-support differential-monomial convolution.**  The `N`-th coefficient of the differential
monomial `∏ₜ f^{(jₜ)}` (arity `r`) is the antidiagonal sum of falling-factorial-weighted products of
source coefficients. -/
theorem coeff_prod_iterate_deriv {r : ℕ} (f : ℂ⟦X⟧) (j : Fin r → ℕ) (N : ℕ) :
    (coeff N) (∏ t, (⇑(d⁄dX ℂ))^[j t] f)
      = ∑ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N,
          ∏ t, (coeff (l t + j t)) f * (((l t + j t).descFactorial (j t) : ℂ)) := by
  classical
  rw [coeff_prod]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.prod_congr rfl fun t _ => coeff_iterate_deriv f (j t) (l t)

end GaloisForLFunctions
