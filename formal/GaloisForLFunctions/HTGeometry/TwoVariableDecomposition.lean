import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative

/-!
# Two-variable polynomials as polynomials in the second variable

An order-zero algebraic differential equation is a two-variable polynomial relation between `z` and
`g z`.  Reading it as a polynomial in the second variable, with coefficients polynomial in the first,
is what lets the algebraic root estimate bound `g`.

The decomposition is the fibrewise grouping of the support by the second exponent — the same device
used for the constituents' equations.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open scoped Classical in
/-- The coefficient of `u^k` in a two-variable polynomial, as a polynomial in the first variable. -/
noncomputable def twoVarCoeff (P : MvPolynomial (Fin 2) ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ m ∈ P.support.filter (fun m => m 1 = k),
    Polynomial.C (MvPolynomial.coeff m P) * Polynomial.X ^ (m 0)

open scoped Classical in
/-- **The two-variable decomposition.**  Evaluating a two-variable polynomial is the same as
evaluating the polynomial in the second variable whose coefficients are `twoVarCoeff`. -/
theorem eval_eq_sum_twoVarCoeff (P : MvPolynomial (Fin 2) ℂ) (d : ℕ)
    (hd : ∀ m ∈ P.support, m 1 ∈ Finset.range (d + 1)) (z u : ℂ) :
    MvPolynomial.eval (fun i : Fin 2 => ![z, u] i) P
      = ∑ k ∈ Finset.range (d + 1), (twoVarCoeff P k).eval z * u ^ k := by
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := P.support)
    (t := Finset.range (d + 1)) (g := fun m : Fin 2 →₀ ℕ => m 1) hd
    (f := fun m : Fin 2 →₀ ℕ => MvPolynomial.coeff m P * (z ^ (m 0) * u ^ (m 1)))
  have hpull : ∀ k ∈ Finset.range (d + 1),
      (twoVarCoeff P k).eval z * u ^ k
      = ∑ m ∈ P.support.filter (fun m => m 1 = k),
          MvPolynomial.coeff m P * (z ^ (m 0) * u ^ (m 1)) := by
    intro k _
    rw [twoVarCoeff, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      (Finset.mem_filter.mp hm).2]
    ring
  rw [Finset.sum_congr rfl hpull, hfiber, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl ?_
  intro m _
  congr 1
  simp [Fin.prod_univ_two]

end GaloisForLFunctions.HTGeometry
