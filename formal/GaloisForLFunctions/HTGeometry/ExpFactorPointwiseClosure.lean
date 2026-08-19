/-
# The exponential-polynomial fibre is closed under pointwise limits with derivatives

The closure statement needs no uniform convergence: what the logarithmic derivative argument uses is
the value and the derivative of the family at finitely many points.  Stating it that way removes the
locally uniform hypothesis, which for a series-defined limit is exactly the hard part.

Main results:
* `exists_poly_limit_of_tendsto_exp_samples` — **the fibre is closed under pointwise convergence of
  values and derivatives at the nodes**.
-/
import GaloisForLFunctions.HTGeometry.ExpPolynomialFactorClosure

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The exponential-polynomial fibre is closed under pointwise convergence of values and
derivatives at the nodes.** -/
theorem exists_poly_limit_of_tendsto_exp_samples {J : ℕ}
    {P : ℕ → Polynomial ℂ} (hdeg : ∀ n, (P n).natDegree ≤ J + 1)
    (hP0 : ∀ n, (P n).coeff 0 = 0)
    {v : Fin (J + 1) → ℂ} (hv : Function.Injective v)
    {G D : Fin (J + 1) → ℂ}
    (hval : ∀ i, Tendsto (fun n => Complex.exp (Polynomial.eval (v i) (P n))) atTop (nhds (G i)))
    (hder : ∀ i, Tendsto
      (fun n => deriv (fun z => Complex.exp (Polynomial.eval z (P n))) (v i)) atTop (nhds (D i)))
    (hGne : ∀ i, G i ≠ 0) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ J + 1 ∧ Q.coeff 0 = 0 ∧
      ∀ h : ℕ, Tendsto (fun n => (P n).coeff h) atTop (nhds (Q.coeff h)) := by
  classical
  have hsamples : ∀ i, Tendsto
      (fun n => Polynomial.eval (v i) (Polynomial.derivative (P n))) atTop
      (nhds (D i / G i)) := by
    intro i
    have hquot := (hder i).div (hval i) (hGne i)
    refine hquot.congr fun n => ?_
    show deriv (fun z => Complex.exp (Polynomial.eval z (P n))) (v i)
        / Complex.exp (Polynomial.eval (v i) (P n))
      = Polynomial.eval (v i) (Polynomial.derivative (P n))
    rw [deriv_exp_polynomial, mul_comm, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one]
  exact exists_limit_of_tendsto_derivative_samples_at hv hdeg hP0 hsamples

end

end GaloisForLFunctions.HTGeometry
