import GaloisForLFunctions.HTGeometry.GomesPolynomialFirstOrderInverse

/-!
# A terminating derivative series for polynomial connection inversion

The degree-descending inverse has a finite exact series. There is no analytic convergence
condition: repeated differentiation eventually vanishes. A remainder identity proves the
formula at every truncation order before specializing to the polynomial degree.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Every truncation of the inverse derivative series has an exact polynomial remainder. -/
theorem gomesPolynomialFirstOrderEquiv_inverse_remainder (a : ℝˣ) (Q : ℝ[X]) (n : ℕ) :
    (gomesPolynomialFirstOrderEquiv a).symm Q =
      -(∑ i ∈ Finset.range n, C ((a : ℝ)⁻¹ ^ (i + 1)) * (derivative^[i]) Q) +
        C ((a : ℝ)⁻¹ ^ n) * (gomesPolynomialFirstOrderEquiv a).symm ((derivative^[n]) Q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (gomesPolynomialFirstOrderEquiv a).symm Q =
          -(∑ i ∈ Finset.range n, C ((a : ℝ)⁻¹ ^ (i + 1)) * (derivative^[i]) Q) +
            C ((a : ℝ)⁻¹ ^ n) * (gomesPolynomialFirstOrderEquiv a).symm ((derivative^[n]) Q) := ih
      _ = _ := by
        rw [gomesPolynomialFirstOrderEquiv_inverse_recursion a ((derivative^[n]) Q),
          Finset.sum_range_succ, Function.iterate_succ_apply']
        simp only [pow_succ, map_mul]
        ring

/-- The actual inverse is a finite derivative series terminating at the forcing degree. -/
theorem gomesPolynomialFirstOrderEquiv_inverse_series (a : ℝˣ) (Q : ℝ[X]) :
    (gomesPolynomialFirstOrderEquiv a).symm Q =
      -(∑ i ∈ Finset.range (Q.natDegree + 1),
        C ((a : ℝ)⁻¹ ^ (i + 1)) * (derivative^[i]) Q) := by
  have h := gomesPolynomialFirstOrderEquiv_inverse_remainder a Q (Q.natDegree + 1)
  simpa only [iterate_derivative_eq_zero (Nat.lt_succ_self Q.natDegree),
    map_zero, mul_zero, add_zero] using h

/-- A coefficient-level finite polynomial resolvent, with no limiting construction. -/
def gomesPolynomialResolventSeries (a : ℝˣ) (Q : ℝ[X]) : ℝ[X] :=
  -(∑ i ∈ Finset.range (Q.natDegree + 1),
    C ((a : ℝ)⁻¹ ^ (i + 1)) * (derivative^[i]) Q)

/-- The finite series solves the full first-order polynomial equation. -/
theorem gomesPolynomialResolventSeries_solves (a : ℝˣ) (Q : ℝ[X]) :
    gomesPolynomialFirstOrderOperator (C (a : ℝ)) (gomesPolynomialResolventSeries a Q) = Q := by
  rw [gomesPolynomialResolventSeries, ← gomesPolynomialFirstOrderEquiv_inverse_series]
  exact gomesPolynomialFirstOrderEquiv_inverse_solves a Q

/-- Applying the series to a polynomial first-order observation recovers its exact input. -/
theorem gomesPolynomialResolventSeries_recovers (a : ℝˣ) (Q : ℝ[X]) :
    gomesPolynomialResolventSeries a (gomesPolynomialFirstOrderOperator (C (a : ℝ)) Q) = Q := by
  rw [gomesPolynomialResolventSeries, ← gomesPolynomialFirstOrderEquiv_inverse_series]
  exact (gomesPolynomialFirstOrderEquiv a).symm_apply_apply Q

/-- Despite its degree-dependent presentation, the finite inverse series is additive. -/
theorem gomesPolynomialResolventSeries_add (a : ℝˣ) (Q R : ℝ[X]) :
    gomesPolynomialResolventSeries a (Q + R) =
      gomesPolynomialResolventSeries a Q + gomesPolynomialResolventSeries a R := by
  simp only [gomesPolynomialResolventSeries, ← gomesPolynomialFirstOrderEquiv_inverse_series, map_add]

/-- Differentiation commutes with the finite inverse series. -/
theorem gomesPolynomialResolventSeries_derivative (a : ℝˣ) (Q : ℝ[X]) :
    (gomesPolynomialResolventSeries a Q).derivative = gomesPolynomialResolventSeries a Q.derivative := by
  simp only [gomesPolynomialResolventSeries, ← gomesPolynomialFirstOrderEquiv_inverse_series,
    gomesPolynomialFirstOrderEquiv_inverse_derivative]

end GaloisForLFunctions.HTGeometry
