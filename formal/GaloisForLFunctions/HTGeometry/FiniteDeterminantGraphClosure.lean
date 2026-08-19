/-
# The closure of the finite-rank determinant graph

On finite rank the full determinant is the order-`g+1` regularized determinant times the exponential
of a polynomial of degree at most `g` vanishing at the origin -- the polynomial whose coefficients
are the first `g` power traces.  So a convergent family of finite-rank determinants whose regularized
determinants also converge differs from the limit of the regularized ones by the exponential of a
polynomial in the same finite-dimensional space, and the polynomial factor converges.

This is the necessity direction of the determinant-completion statement, in the finite-rank
category: nothing beyond the first `g` power traces survives, and exactly those `g` coordinates do.

Main results:
* `tracePolynomial`, `eval_tracePolynomial` — the polynomial of the first `g` power traces.
* `det_one_add_smul_eq_finiteDetOrder_mul_exp` — **the factorisation on finite rank**.
* `exists_poly_limit_of_tendsto_finiteDet` — **the closure of the determinant graph**.
-/
import GaloisForLFunctions.HTGeometry.ExpPolynomialFactorClosure
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminantOrder
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The polynomial whose coefficients are the first `g` power traces. -/
def tracePolynomial (g : ℕ) (M : Matrix m m ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range g,
    Polynomial.C (-((-1 : ℂ) ^ (j + 1) * (M ^ (j + 1)).trace / ((j + 1 : ℕ) : ℂ)))
      * Polynomial.X ^ (j + 1)

theorem coeff_tracePolynomial (g : ℕ) (M : Matrix m m ℂ) (h : ℕ) :
    (tracePolynomial g M).coeff h
      = ∑ j ∈ Finset.range g,
          (if h = j + 1 then -((-1 : ℂ) ^ (j + 1) * (M ^ (j + 1)).trace / ((j + 1 : ℕ) : ℂ))
            else 0) := by
  rw [tracePolynomial, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hj : h = j + 1 <;> simp [hj]

theorem coeff_tracePolynomial_zero (g : ℕ) (M : Matrix m m ℂ) :
    (tracePolynomial g M).coeff 0 = 0 := by
  rw [coeff_tracePolynomial]
  exact Finset.sum_eq_zero fun j _ => by simp

theorem natDegree_tracePolynomial_le (g : ℕ) (M : Matrix m m ℂ) :
    (tracePolynomial g M).natDegree ≤ g := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun h hh => ?_
  rw [coeff_tracePolynomial]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjg : j < g := Finset.mem_range.mp hj
  rw [if_neg (by omega)]

theorem eval_tracePolynomial (g : ℕ) (M : Matrix m m ℂ) (z : ℂ) :
    Polynomial.eval z (tracePolynomial g M)
      = -∑ j ∈ Finset.range g, (-z) ^ (j + 1) * (M ^ (j + 1)).trace / ((j + 1 : ℕ) : ℂ) := by
  rw [tracePolynomial, Polynomial.eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, neg_pow]
  ring

/-- **The factorisation on finite rank.**  The full determinant is the order-`g+1` regularized
determinant times the exponential of the power-trace polynomial. -/
theorem det_one_add_smul_eq_finiteDetOrder_mul_exp (g : ℕ) (M : Matrix m m ℂ) (z : ℂ) :
    (1 + z • M).det
      = finiteDetOrder g M z * Complex.exp (Polynomial.eval z (tracePolynomial g M)) := by
  rw [finiteDetOrder, mul_assoc, ← Complex.exp_add, eval_tracePolynomial, add_neg_cancel,
    Complex.exp_zero, mul_one]

/-- The finite-rank determinant is analytic in the parameter. -/
theorem analyticAt_det_one_add_smul (M : Matrix m m ℂ) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (1 + z • M).det) z₀ := by
  refine analyticAt_matrix_det_parametric fun i j => ?_
  have hent : (fun z : ℂ => (1 + z • M) i j)
      = fun z : ℂ => (1 : Matrix m m ℂ) i j + z * M i j := by
    funext z
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hent]
  exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)

/-- The order-`g+1` regularized determinant is analytic in the parameter. -/
theorem analyticAt_finiteDetOrder (g : ℕ) (M : Matrix m m ℂ) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => finiteDetOrder g M z) z₀ := by
  have hexp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (∑ j ∈ Finset.range g,
      (-z) ^ (j + 1) * (M ^ (j + 1)).trace / ((j + 1 : ℕ) : ℂ))) z₀ := by
    refine analyticAt_cexp.comp ?_
    refine Finset.analyticAt_fun_sum _ fun j _ => ?_
    have hterm : (fun z : ℂ => (-z) ^ (j + 1) * (M ^ (j + 1)).trace / ((j + 1 : ℕ) : ℂ))
        = fun z : ℂ => (-z) ^ (j + 1) * ((M ^ (j + 1)).trace / ((j + 1 : ℕ) : ℂ)) := by
      funext z
      rw [mul_div_assoc]
    rw [hterm]
    exact ((analyticAt_id.neg).pow (j + 1)).mul analyticAt_const
  have hdet := analyticAt_det_one_add_smul M z₀
  have hprod := hdet.mul hexp
  refine hprod.congr ?_
  filter_upwards with z
  rw [finiteDetOrder]
  rfl

/-- **The closure of the finite-rank determinant graph.**  If the finite-rank determinants and
their order-`J+2` regularizations both converge locally uniformly on an open set, and both limits
are nonzero at `J+1` distinct points of it, then the two limits differ by the exponential of a
polynomial of degree at most `J+1` vanishing at the origin. -/
theorem exists_poly_limit_of_tendsto_finiteDet {J : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {M : ℕ → Matrix m m ℂ} {F E : ℂ → ℂ}
    (hF : TendstoLocallyUniformlyOn (fun n z => (1 + z • M n).det) F atTop U)
    (hE : TendstoLocallyUniformlyOn (fun n z => finiteDetOrder (J + 1) (M n) z) E atTop U)
    {v : Fin (J + 1) → ℂ} (hv : Function.Injective v) (hvU : ∀ i, v i ∈ U)
    (hFne : ∀ i, F (v i) ≠ 0) (hEne : ∀ i, E (v i) ≠ 0) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ J + 1 ∧ Q.coeff 0 = 0 ∧
      ∀ z ∈ U, F z = E z * Complex.exp (Polynomial.eval z Q) := by
  classical
  set P : ℕ → Polynomial ℂ := fun n => tracePolynomial (J + 1) (M n) with hPdef
  have hdeg : ∀ n, (P n).natDegree ≤ J + 1 := fun n => natDegree_tracePolynomial_le _ _
  have hP0 : ∀ n, (P n).coeff 0 = 0 := fun n => coeff_tracePolynomial_zero _ _
  have hfac : ∀ (n : ℕ) (z : ℂ),
      (1 + z • M n).det
        = finiteDetOrder (J + 1) (M n) z * Complex.exp (Polynomial.eval z (P n)) :=
    fun n z => det_one_add_smul_eq_finiteDetOrder_mul_exp (J + 1) (M n) z
  have hFderiv := hF.deriv (Filter.Eventually.of_forall fun n =>
      fun z _ => ((analyticAt_det_one_add_smul (M n) z).differentiableAt).differentiableWithinAt)
    hU
  have hEderiv := hE.deriv (Filter.Eventually.of_forall fun n =>
      fun z _ =>
        ((analyticAt_finiteDetOrder (J + 1) (M n) z).differentiableAt).differentiableWithinAt) hU
  have hderivid : ∀ (n : ℕ) (z : ℂ),
      deriv (fun w : ℂ => (1 + w • M n).det) z
        = deriv (fun w : ℂ => finiteDetOrder (J + 1) (M n) w) z
              * Complex.exp (Polynomial.eval z (P n))
          + finiteDetOrder (J + 1) (M n) z
              * (Complex.exp (Polynomial.eval z (P n))
                * Polynomial.eval z (Polynomial.derivative (P n))) := by
    intro n z
    have hfun : (fun w : ℂ => (1 + w • M n).det)
        = fun w : ℂ => finiteDetOrder (J + 1) (M n) w
            * Complex.exp (Polynomial.eval w (P n)) := by
      funext w
      exact hfac n w
    rw [hfun]
    have hE' : HasDerivAt (fun w : ℂ => finiteDetOrder (J + 1) (M n) w)
        (deriv (fun w : ℂ => finiteDetOrder (J + 1) (M n) w) z) z :=
      (analyticAt_finiteDetOrder (J + 1) (M n) z).differentiableAt.hasDerivAt
    have hx : HasDerivAt (fun w : ℂ => Complex.exp (Polynomial.eval w (P n)))
        (Complex.exp (Polynomial.eval z (P n))
          * Polynomial.eval z (Polynomial.derivative (P n))) z :=
      ((P n).hasDerivAt z).cexp
    exact (hE'.mul hx).deriv
  have hsamples : ∀ i, Tendsto
      (fun n => Polynomial.eval (v i) (Polynomial.derivative (P n))) atTop
      (nhds (deriv F (v i) / F (v i) - deriv E (v i) / E (v i))) := by
    intro i
    have hFn : Tendsto (fun n => (1 + (v i) • M n).det) atTop (nhds (F (v i))) :=
      hF.tendsto_at (hvU i)
    have hEn : Tendsto (fun n => finiteDetOrder (J + 1) (M n) (v i)) atTop (nhds (E (v i))) :=
      hE.tendsto_at (hvU i)
    have hFn' : Tendsto (fun n => deriv (fun w : ℂ => (1 + w • M n).det) (v i)) atTop
        (nhds (deriv F (v i))) := hFderiv.tendsto_at (hvU i)
    have hEn' : Tendsto (fun n => deriv (fun w : ℂ => finiteDetOrder (J + 1) (M n) w) (v i))
        atTop (nhds (deriv E (v i))) := hEderiv.tendsto_at (hvU i)
    have hq1 : Tendsto (fun n => deriv (fun w : ℂ => (1 + w • M n).det) (v i)
        / (1 + (v i) • M n).det) atTop (nhds (deriv F (v i) / F (v i))) := by
      have := hFn'.div hFn (hFne i)
      exact this
    have hq2 : Tendsto (fun n => deriv (fun w : ℂ => finiteDetOrder (J + 1) (M n) w) (v i)
        / finiteDetOrder (J + 1) (M n) (v i)) atTop (nhds (deriv E (v i) / E (v i))) := by
      have := hEn'.div hEn (hEne i)
      exact this
    have hne : ∀ᶠ n in (atTop : Filter ℕ), finiteDetOrder (J + 1) (M n) (v i) ≠ 0 :=
      hEn.eventually_ne (hEne i)
    refine Filter.Tendsto.congr' ?_ (hq1.sub hq2)
    filter_upwards [hne] with n hn
    have hexpne : Complex.exp (Polynomial.eval (v i) (P n)) ≠ 0 := Complex.exp_ne_zero _
    have hdetne : (1 + (v i) • M n).det ≠ 0 := by
      rw [hfac n (v i)]
      exact mul_ne_zero hn hexpne
    rw [hderivid n (v i), hfac n (v i)]
    field_simp
    ring
  obtain ⟨Q, hQdeg, hQ0, hQcoeff⟩ :=
    exists_limit_of_tendsto_derivative_samples_at hv hdeg hP0 hsamples
  refine ⟨Q, hQdeg, hQ0, fun z hz => ?_⟩
  have h1 : Tendsto (fun n => (1 + z • M n).det) atTop (nhds (F z)) := hF.tendsto_at hz
  have h2 : Tendsto (fun n => finiteDetOrder (J + 1) (M n) z) atTop (nhds (E z)) :=
    hE.tendsto_at hz
  have h3 : Tendsto (fun n => Polynomial.eval z (P n)) atTop (nhds (Polynomial.eval z Q)) :=
    tendsto_eval_of_tendsto_coeff hdeg hQdeg hQcoeff z
  have h4 : Tendsto (fun n => Complex.exp (Polynomial.eval z (P n))) atTop
      (nhds (Complex.exp (Polynomial.eval z Q))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp h3
  refine tendsto_nhds_unique h1 ?_
  refine Filter.Tendsto.congr (fun n => (hfac n z).symm) ?_
  exact h2.mul h4

end

end GaloisForLFunctions.HTGeometry
