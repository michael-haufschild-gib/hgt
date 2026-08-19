/-
# The exponential-polynomial fibre is closed under locally uniform limits

A family of exponentials of normalized bounded-degree polynomials, converging locally uniformly to
a limit that does not vanish at enough points, converges *as polynomials*: the derivative of the
limit divided by the limit is the limiting logarithmic derivative, the normalization pins the
constant term, and the finite-dimensional polynomial space is closed.  The limit function is again
the exponential of such a polynomial.

This is the closure statement behind a determinant completion: the polynomial factor of a
convergent family of finite-rank determinants converges to a polynomial factor of the same degree
bound.

Main results:
* `deriv_exp_polynomial` — the derivative of the exponential of a polynomial.
* `exists_poly_limit_of_tendstoLocallyUniformlyOn_exp` — **the fibre is closed**.
-/
import GaloisForLFunctions.HTGeometry.GeneralNodePolynomialLimit

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem deriv_exp_polynomial (p : Polynomial ℂ) (x : ℂ) :
    deriv (fun z => Complex.exp (Polynomial.eval z p)) x
      = Complex.exp (Polynomial.eval x p) * Polynomial.eval x (Polynomial.derivative p) :=
  ((p.hasDerivAt x).cexp).deriv

theorem differentiableOn_exp_polynomial (p : Polynomial ℂ) (U : Set ℂ) :
    DifferentiableOn ℂ (fun z => Complex.exp (Polynomial.eval z p)) U :=
  (Complex.differentiable_exp.comp p.differentiable).differentiableOn

/-- **The exponential-polynomial fibre is closed under locally uniform limits.** -/
theorem exists_poly_limit_of_tendstoLocallyUniformlyOn_exp {J : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {P : ℕ → Polynomial ℂ} (hdeg : ∀ n, (P n).natDegree ≤ J + 1)
    (hP0 : ∀ n, (P n).coeff 0 = 0) {G : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => Complex.exp (Polynomial.eval z (P n))) G atTop U)
    {v : Fin (J + 1) → ℂ} (hv : Function.Injective v) (hvU : ∀ i, v i ∈ U)
    (hG : ∀ i, G (v i) ≠ 0) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ J + 1 ∧ Q.coeff 0 = 0 ∧
      (∀ h : ℕ, Tendsto (fun n => (P n).coeff h) atTop (nhds (Q.coeff h))) ∧
      ∀ z ∈ U, G z = Complex.exp (Polynomial.eval z Q) := by
  classical
  have hdiff : ∀ᶠ n in (atTop : Filter ℕ),
      DifferentiableOn ℂ (fun z => Complex.exp (Polynomial.eval z (P n))) U :=
    Filter.Eventually.of_forall fun n => differentiableOn_exp_polynomial (P n) U
  have hderiv := hconv.deriv hdiff hU
  have hsamples : ∀ i, Tendsto
      (fun n => Polynomial.eval (v i) (Polynomial.derivative (P n))) atTop
      (nhds (deriv G (v i) / G (v i))) := by
    intro i
    have hnum : Tendsto
        (fun n => deriv (fun z => Complex.exp (Polynomial.eval z (P n))) (v i)) atTop
        (nhds (deriv G (v i))) := hderiv.tendsto_at (hvU i)
    have hden : Tendsto (fun n => Complex.exp (Polynomial.eval (v i) (P n))) atTop
        (nhds (G (v i))) := hconv.tendsto_at (hvU i)
    have hquot := hnum.div hden (hG i)
    refine hquot.congr fun n => ?_
    show deriv (fun z => Complex.exp (Polynomial.eval z (P n))) (v i)
        / Complex.exp (Polynomial.eval (v i) (P n))
      = Polynomial.eval (v i) (Polynomial.derivative (P n))
    rw [deriv_exp_polynomial, mul_comm, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one]
  obtain ⟨Q, hQdeg, hQ0, hQcoeff⟩ :=
    exists_limit_of_tendsto_derivative_samples_at hv hdeg hP0 hsamples
  refine ⟨Q, hQdeg, hQ0, hQcoeff, fun z hz => ?_⟩
  have h1 : Tendsto (fun n => Complex.exp (Polynomial.eval z (P n))) atTop (nhds (G z)) :=
    hconv.tendsto_at hz
  have h2 : Tendsto (fun n => Polynomial.eval z (P n)) atTop
      (nhds (Polynomial.eval z Q)) :=
    tendsto_eval_of_tendsto_coeff hdeg hQdeg hQcoeff z
  exact tendsto_nhds_unique h1 (Complex.continuous_exp.continuousAt.tendsto.comp h2)

end

end GaloisForLFunctions.HTGeometry
