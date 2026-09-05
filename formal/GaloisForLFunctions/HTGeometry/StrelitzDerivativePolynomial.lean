import GaloisForLFunctions.HTGeometry.StrelitzMaximumModulusSet
import GaloisForLFunctions.HTGeometry.StrelitzHeatLeadingDecay
import GaloisForLFunctions.HTGeometry.LastVariableJetLift

/-!
# Strelitz relation as a polynomial in the Euler derivative

The corpus's exact `jetUnlift` equivalence splits the last variable without rebuilding another
support decomposition.  Applied to the leading logarithmic-jet relation, it produces a nonzero
univariate polynomial in `v = z u'`, with coefficients polynomial in `(z,u)`.  Specializing those
coefficients and evaluating at `v` recovers the original relation exactly.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Read a two-variable logarithmic-jet polynomial as a univariate polynomial in its last variable
with coefficients in the first variable and the independent-variable coefficient ring. -/
def strelitzDerivativePolynomial
    (P : MvPolynomial (Fin 2) (Polynomial ℂ)) :
    Polynomial (MvPolynomial (Fin 1) (Polynomial ℂ)) :=
  jetUnlift P

/-- Specialize the coefficient variable at `z` and the first logarithmic jet at `U`, leaving a
complex polynomial in the Euler derivative variable. -/
def strelitzDerivativeSpecialization
    (R : Polynomial (MvPolynomial (Fin 1) (Polynomial ℂ)))
    (z U : ℂ) : Polynomial ℂ :=
  R.map (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) ![U])

/-- Splitting the last variable preserves nonzeroness. -/
theorem strelitzDerivativePolynomial_ne_zero
    {P : MvPolynomial (Fin 2) (Polynomial ℂ)} (hP : P ≠ 0) :
    strelitzDerivativePolynomial P ≠ 0 :=
  jetUnlift_ne_zero hP

/-- Specialization followed by evaluation at the Euler derivative recovers simultaneous
two-variable evaluation exactly. -/
theorem eval_strelitzDerivativeSpecialization
    (P : MvPolynomial (Fin 2) (Polynomial ℂ)) (z U V : ℂ) :
    (strelitzDerivativeSpecialization (strelitzDerivativePolynomial P) z U).eval V =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V] P := by
  have hlift : ∀ A : Polynomial (MvPolynomial (Fin 1) (Polynomial ℂ)),
      MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
          (lastVariableJetLift A) =
        Polynomial.eval₂
          (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) ![U]) V A := by
    intro A
    induction A using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [jetLift_add, MvPolynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
    | monomial k A =>
        rw [jetLift_monomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_rename,
          MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, Polynomial.eval₂_monomial]
        change MvPolynomial.eval₂ (Polynomial.evalRingHom z)
            ((![U, V] : Fin 2 → ℂ) ∘ Fin.castSucc) A * V ^ k =
          MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U] A * V ^ k
        congr 2
        funext i
        fin_cases i
        rfl
  rw [strelitzDerivativeSpecialization, strelitzDerivativePolynomial, Polynomial.eval_map]
  calc
    Polynomial.eval₂ (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) ![U]) V
        (jetUnlift P) =
        MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
          (lastVariableJetLift (jetUnlift P)) := (hlift (jetUnlift P)).symm
    _ = MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V] P := by
      rw [lastVariableJetLift_jetUnlift]

open Filter GaloisForLFunctions

variable {a : ℕ → ℂ}

/-- **Univariate derivative-polynomial Newton input retaining the full maximum-circle property.**
An assumed order-two entire-heat ADE
produces a fixed nonzero polynomial in `v = z u'`, with coefficients polynomial in `(z,u)`, whose
specialized value at the Wiman jets decays faster than every inverse radius power. -/
theorem exists_nonzero_strelitzDerivativePolynomial_superpolynomiallySmall_of_order_two_entireHeat_isMaximumOnCircle
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ R : Polynomial (MvPolynomial (Fin 1) (Polynomial ℂ)), R ≠ 0 ∧
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
          ‖(strelitzDerivativeSpecialization R (z n)
            (eulerLogDeriv (coeffFun a) (z n))).eval
              (eulerLogDerivSecond (coeffFun a) (z n))‖ *
            (Real.exp (x n)) ^ j) atTop (nhds 0)) ∧
        ∀ n : ℕ, ∀ w : ℂ, ‖w‖ = ‖z n‖ →
          ‖coeffFun a w‖ ≤ ‖coeffFun a (z n)‖ := by
  obtain ⟨P, hP, x, z, hx, hz, hfloor, hfz, hu, hv, hsmall, hmaxCircle⟩ :=
    exists_nonzero_strelitzLogJetPolynomial_superpolynomiallySmall_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  refine ⟨strelitzDerivativePolynomial P, strelitzDerivativePolynomial_ne_zero hP,
    x, z, hx, hz, hfloor, hfz, hu, hv, ?_, hmaxCircle⟩
  intro j
  simpa only [eval_strelitzDerivativeSpecialization] using hsmall j

/-- **Univariate derivative-polynomial Newton input.** An assumed order-two entire-heat ADE
produces a fixed nonzero polynomial in `v = z u'`, with coefficients polynomial in `(z,u)`, whose
specialized value at the Wiman jets decays faster than every inverse radius power. -/
theorem exists_nonzero_strelitzDerivativePolynomial_superpolynomiallySmall_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ R : Polynomial (MvPolynomial (Fin 1) (Polynomial ℂ)), R ≠ 0 ∧
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
          ‖(strelitzDerivativeSpecialization R (z n)
            (eulerLogDeriv (coeffFun a) (z n))).eval
              (eulerLogDerivSecond (coeffFun a) (z n))‖ *
            (Real.exp (x n)) ^ j) atTop (nhds 0) := by
  obtain ⟨R, hR, x, z, hx, hz, hfloor, hfz, hu, hv, hsmall, _⟩ :=
    exists_nonzero_strelitzDerivativePolynomial_superpolynomiallySmall_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  exact ⟨R, hR, x, z, hx, hz, hfloor, hfz, hu, hv, hsmall⟩

end

end GaloisForLFunctions.HTGeometry
