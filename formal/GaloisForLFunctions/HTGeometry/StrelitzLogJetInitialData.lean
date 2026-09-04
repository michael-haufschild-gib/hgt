import GaloisForLFunctions.HTGeometry.StrelitzLogJetWimanAsymptotic

/-!
# Exact initial data for the Strelitz order-two reduction

An order-two ADE and an infinite entire coefficient sequence determine one fixed nonzero
logarithmic-jet polynomial and a sequence of exact roots at escaping Wiman--Valiron points.  The
relative errors are tied to `1/(n+1)`, so no later diagonal selection is required.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {a : ℕ → ℂ}

/-- **Strelitz initial-data package.** The polynomial is fixed and nonzero, its value is exactly
zero at every selected point, the logarithmic radii escape at least linearly, and both logarithmic
jet defects have explicit vanishing relative errors. -/
theorem exists_strelitzLogJetInitialData_of_order_two
    (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ Q : MvPolynomial (Fin 3) (Polynomial ℂ), Q ≠ 0 ∧
      ∃ (x : ℕ → ℝ) (z : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, MvPolynomial.eval₂ (Polynomial.evalRingHom (z n))
          ![coeffFun a (z n), eulerLogDeriv (coeffFun a) (z n),
            eulerLogDerivSecond (coeffFun a) (z n)] Q = 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        ∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2 := by
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  obtain ⟨Q, hQ, hrel⟩ :=
    exists_strelitzLogJetRelation_of_differentiallyAlgebraicOfOrder_two
      (GaloisForLFunctions.Nevanlinna.analyticOnNhd_coeffFun ha) hDA
  have hpoint : ∀ n : ℕ, ∃ y, (n : ℝ) ≤ y ∧ ∃ w : ℂ, ‖w‖ = Real.exp y ∧
      maxTerm a (Real.exp y) ≤ ‖coeffFun a w‖ ∧ coeffFun a w ≠ 0 ∧
      ‖eulerLogDeriv (coeffFun a) w - (centralIndex a (Real.exp y) : ℂ)‖
        ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp y) : ℝ) ∧
      ‖eulerLogDerivSecond (coeffFun a) w‖
        ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp y) : ℝ) ^ 2 := by
    intro n
    exact exists_radius_point_eulerLogDerivSecond_small ha hn₀ htrans
      (by positivity : 0 < (1 / ((n : ℝ) + 1))) n
  choose x hx z hz hfloor hfz hu hv using hpoint
  exact ⟨Q, hQ, x, z, hx, hz, hfloor, hfz, fun n => hrel (z n) (hfz n), hu, hv⟩

end GaloisForLFunctions.HTGeometry
