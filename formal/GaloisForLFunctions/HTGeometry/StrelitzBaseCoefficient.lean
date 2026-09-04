import GaloisForLFunctions.HTGeometry.StrelitzDerivativePolynomial

/-!
# The highest independent-variable coefficient in the Strelitz relation

Specializing the two logarithmic jet variables while retaining the independent variable gives a
univariate polynomial in `z`.  Its coefficient of every `z^k` is the evaluation of one fixed
bivariate complex polynomial.  In particular, the coefficient at the largest coefficient degree
is a nonzero polynomial, so the first Newton face cannot disappear during specialization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Specialize the two logarithmic jet variables while retaining the coefficient variable `z`. -/
def strelitzBaseSpecialization
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) (x : Fin 2 → ℂ) : Polynomial ℂ :=
  ∑ e ∈ Q.support, Q.coeff e * Polynomial.C (e.prod fun i k => x i ^ k)

/-- The fixed bivariate polynomial giving the coefficient of `z^k` after jet specialization. -/
def strelitzBaseCoefficient
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) (k : ℕ) : MvPolynomial (Fin 2) ℂ :=
  ∑ e ∈ Q.support, MvPolynomial.monomial e ((Q.coeff e).coeff k)

/-- Evaluating the retained-`z` polynomial recovers simultaneous evaluation of the relation. -/
theorem eval_strelitzBaseSpecialization
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) (z : ℂ) (x : Fin 2 → ℂ) :
    (strelitzBaseSpecialization Q x).eval z =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z) x Q := by
  classical
  rw [strelitzBaseSpecialization, Polynomial.eval_finsetSum, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  rfl

/-- Coefficient extraction commutes with specialization of the logarithmic jet variables. -/
theorem coeff_strelitzBaseSpecialization
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) (x : Fin 2 → ℂ) (k : ℕ) :
    (strelitzBaseSpecialization Q x).coeff k =
      MvPolynomial.eval x (strelitzBaseCoefficient Q k) := by
  classical
  rw [strelitzBaseSpecialization, Polynomial.finsetSum_coeff,
    strelitzBaseCoefficient, map_sum]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [Polynomial.coeff_mul_C, MvPolynomial.eval_monomial]

/-- Distinct jet monomials recover the source coefficient at every `z`-degree. -/
theorem coeff_strelitzBaseCoefficient
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) (k : ℕ) (e : Fin 2 →₀ ℕ) :
    (strelitzBaseCoefficient Q k).coeff e =
      if e ∈ Q.support then (Q.coeff e).coeff k else 0 := by
  classical
  rw [strelitzBaseCoefficient, MvPolynomial.coeff_sum]
  by_cases he : e ∈ Q.support
  · rw [if_pos he]
    refine Finset.sum_eq_single_of_mem e he ?_ |>.trans ?_
    · intro d hd hde
      rw [MvPolynomial.coeff_monomial, if_neg hde]
    · simp
  · rw [if_neg he]
    refine Finset.sum_eq_zero ?_
    intro d hd
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h => he (h ▸ hd)

/-- The coefficient face at the largest `z`-degree is nonzero. -/
theorem strelitzBaseCoefficient_polynomialMvCoeffDegree_ne_zero
    {Q : MvPolynomial (Fin 2) (Polynomial ℂ)} (hQ : Q ≠ 0) :
    strelitzBaseCoefficient Q (polynomialMvCoeffDegree Q) ≠ 0 := by
  classical
  obtain ⟨e, he, hdeg⟩ :=
    Finset.exists_mem_eq_sup Q.support (MvPolynomial.support_nonempty.mpr hQ)
      (fun d => (Q.coeff d).natDegree)
  intro hzero
  have hc : (strelitzBaseCoefficient Q (polynomialMvCoeffDegree Q)).coeff e = 0 := by
    rw [hzero]
    simp
  rw [coeff_strelitzBaseCoefficient, if_pos he, polynomialMvCoeffDegree, hdeg] at hc
  exact Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he) hc

open Filter GaloisForLFunctions

variable {a : ℕ → ℂ}

/-- **Highest-`z` Strelitz face retaining the full maximum-circle property.**
An assumed order-two entire-heat ADE has a fixed nonzero highest
`z`-coefficient face in the two logarithmic jet variables, while the exact polynomial in `z`
remains superpolynomially small along the selected Wiman sequence. -/
theorem exists_nonzero_strelitzBaseCoefficient_of_order_two_entireHeat_isMaximumOnCircle
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ P : MvPolynomial (Fin 2) (Polynomial ℂ), P ≠ 0 ∧
      strelitzBaseCoefficient P (polynomialMvCoeffDegree P) ≠ 0 ∧
      ∃ (x : ℕ → ℝ) (z : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        (∀ j : ℕ, Tendsto (fun n : ℕ =>
          ‖(strelitzBaseSpecialization P
            ![eulerLogDeriv (coeffFun a) (z n),
              eulerLogDerivSecond (coeffFun a) (z n)]).eval (z n)‖ *
            (Real.exp (x n)) ^ j) atTop (nhds 0)) ∧
        ∀ n : ℕ, ∀ w : ℂ, ‖w‖ = ‖z n‖ →
          ‖coeffFun a w‖ ≤ ‖coeffFun a (z n)‖ := by
  obtain ⟨P, hP, x, z, hx, hz, hfloor, hfz, hu, hv, hsmall, hmaxCircle⟩ :=
    exists_nonzero_strelitzLogJetPolynomial_superpolynomiallySmall_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  refine ⟨P, hP, strelitzBaseCoefficient_polynomialMvCoeffDegree_ne_zero hP,
    x, z, hx, hz, hfloor, hfz, hu, hv, ?_, hmaxCircle⟩
  intro j
  simpa only [eval_strelitzBaseSpecialization] using hsmall j

/-- **Highest-`z` Strelitz face.** An assumed order-two entire-heat ADE has a fixed nonzero highest
`z`-coefficient face in the two logarithmic jet variables, while the exact polynomial in `z`
remains superpolynomially small along the selected Wiman sequence. -/
theorem exists_nonzero_strelitzBaseCoefficient_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ P : MvPolynomial (Fin 2) (Polynomial ℂ), P ≠ 0 ∧
      strelitzBaseCoefficient P (polynomialMvCoeffDegree P) ≠ 0 ∧
      ∃ (x : ℕ → ℝ) (z : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        ∀ j : ℕ, Tendsto (fun n : ℕ =>
          ‖(strelitzBaseSpecialization P
            ![eulerLogDeriv (coeffFun a) (z n),
              eulerLogDerivSecond (coeffFun a) (z n)]).eval (z n)‖ *
            (Real.exp (x n)) ^ j) atTop (nhds 0) := by
  obtain ⟨P, hP, hface, x, z, hx, hz, hfloor, hfz, hu, hv, hsmall, _⟩ :=
    exists_nonzero_strelitzBaseCoefficient_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  exact ⟨P, hP, hface, x, z, hx, hz, hfloor, hfz, hu, hv, hsmall⟩

end

end GaloisForLFunctions.HTGeometry
