import GaloisForLFunctions.HTGeometry.CascadeOrderTheorem

/-!
# First-order equations as multivariate polynomials

The card writes a first-order algebraic differential equation as a finite sum
`∑ a_p(z)·g(z)^{p₁}·g'(z)^{p₂} = 0`.  The corpus's notion of differential order uses a multivariate
polynomial in `(z, g, g')`.  This file builds the second from the first and checks that the two
evaluate to the same thing, so a constituent's equation can be fed to `DifferentiallyAlgebraicOfOrder`
directly.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The multivariate polynomial of a first-order relation: `z ↦ X 0`, `g ↦ X 1`, `g' ↦ X 2`. -/
noncomputable def firstOrderMvPoly (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) :
    MvPolynomial (Fin 3) ℂ :=
  ∑ p ∈ S, Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (A p)
    * (MvPolynomial.X 1) ^ p.1 * (MvPolynomial.X 2) ^ p.2

/-- **The evaluation of the constructed polynomial.** -/
theorem eval_firstOrderMvPoly (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (z u v : ℂ) :
    MvPolynomial.eval (fun j : Fin 3 => ![z, u, v] j) (firstOrderMvPoly S A)
      = ∑ p ∈ S, (A p).eval z * u ^ p.1 * v ^ p.2 := by
  classical
  rw [firstOrderMvPoly, map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [map_mul, map_mul, map_pow, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_X]
  congr 1
  congr 1
  · induction (A p) using Polynomial.induction_on' with
    | add q r ihq ihr =>
        rw [Polynomial.eval₂_add, map_add, ihq, ihr, Polynomial.eval_add]
    | monomial k c =>
        rw [Polynomial.eval₂_monomial, map_mul, map_pow, MvPolynomial.eval_C,
          MvPolynomial.eval_X, Polynomial.eval_monomial]
        rfl

/-- **A first-order relation is an order-one algebraic differential equation.** -/
theorem differentiallyAlgebraicOfOrder_one_of_relation {g : ℂ → ℂ}
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ}
    (hP0 : firstOrderMvPoly S A ≠ 0)
    (hrel : ∀ u : ℂ, ∑ p ∈ S, (A p).eval u * (g u) ^ p.1 * (deriv g u) ^ p.2 = 0) :
    DifferentiallyAlgebraicOfOrder g 1 := by
  refine ⟨firstOrderMvPoly S A, hP0, ?_⟩
  intro z
  have hvec : (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) g z)
      = fun j : Fin 3 => ![z, g z, deriv g z] j := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · rw [Fin.cons_succ]
      fin_cases i <;> simp [iteratedDeriv_zero, iteratedDeriv_one]
  rw [hvec, eval_firstOrderMvPoly]
  exact hrel z

/-! ## Order zero is algebraicity

An order-zero equation is a polynomial relation between `z` and `g` alone.  The corpus's pointwise
algebraic root estimate then bounds `g` by the normalised coefficients, so an entire solution has
polynomial growth off the leading coefficient's zeros — which is why the order-zero case of the
cascade theorem is the statement that a transcendental entire function is not algebraic. -/

/-- **The growth bound from an order-zero relation.**  At a point where the leading coefficient does
not vanish, the value is controlled by the normalised lower coefficients. -/
theorem posLog_norm_le_of_order_zero {g : ℂ → ℂ} {d : ℕ} {a : ℕ → ℂ → ℂ} (hd : 1 ≤ d)
    {z : ℂ} (had : a d z ≠ 0)
    (hrel : ∑ k ∈ Finset.range (d + 1), a k z * (g z) ^ k = 0) :
    Real.posLog ‖g z‖ ≤ Real.posLog (∑ k ∈ Finset.range d, ‖a k z / a d z‖) :=
  posLog_norm_le_of_root hd had hrel

/-- **The order-zero relation as a bound by the coefficient sum.** -/
theorem norm_le_of_order_zero {g : ℂ → ℂ} {d : ℕ} {a : ℕ → ℂ → ℂ} (hd : 1 ≤ d)
    {z : ℂ} (had : a d z ≠ 0)
    (hrel : ∑ k ∈ Finset.range (d + 1), a k z * (g z) ^ k = 0) :
    ‖g z‖ ≤ max 1 (∑ k ∈ Finset.range d, ‖a k z / a d z‖) :=
  norm_le_max_sum_of_root hd had hrel

end GaloisForLFunctions.HTGeometry
