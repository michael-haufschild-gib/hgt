import GaloisForLFunctions.HTGeometry.RankDefectAlgebraicCore
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Independence of node powers times distinct monomials

The expanded evaluation matrix has entries `z ^ d * M β (y)`, indexed by a monomial `β` and a
coefficient degree `d`.  The multi-row rank condition needs this family to be linearly independent
as functions of the pair `(z, y)`.

It is, and the argument separates the two variables.  Fixing `y`, a vanishing combination is a
polynomial in `z` vanishing identically on `ℂ`, so each of its coefficients vanishes; each such
coefficient is a combination of distinct monomials in `y`, which vanishes identically only if its
coefficients do.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A combination of distinct monomials vanishing at every point has zero coefficients. -/
theorem monomial_coeffs_eq_zero_of_eval_eq_zero
    {σ κ : Type*} [Fintype κ] [DecidableEq κ]
    (exponent : κ → (σ →₀ ℕ)) (hexp : Function.Injective exponent)
    (a : κ → ℂ)
    (h : ∀ y : σ → ℂ,
      MvPolynomial.eval y (∑ β : κ, MvPolynomial.monomial (exponent β) (a β)) = 0) :
    ∀ β, a β = 0 := by
  classical
  intro β
  by_contra hβ
  have hzero : (∑ β : κ, MvPolynomial.monomial (exponent β) (a β)) = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [h y, map_zero]
  exact sum_monomial_ne_zero exponent hexp a hβ hzero

/-- Powers of a complex variable are detected coefficientwise: a polynomial combination vanishing
at every point has vanishing coefficients. -/
theorem powerCoeffs_eq_zero_of_eval_eq_zero {q : ℕ} (a : Fin (q + 1) → ℂ)
    (h : ∀ z : ℂ, ∑ d : Fin (q + 1), a d * z ^ (d : ℕ) = 0) :
    ∀ d, a d = 0 := by
  classical
  intro d
  by_contra hd
  have hpoly : rowCoefficientPoly q (fun p : Unit × Fin (q + 1) => a p.2) () ≠ 0 :=
    rowCoefficientPoly_ne_zero q (fun p : Unit × Fin (q + 1) => a p.2) () hd
  apply hpoly
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_zero, eval_rowCoefficientPoly, rowCoefficientPolynomial]
  exact h z

/-- **Independence of node powers times distinct monomials.**  The family
`(β, d) ↦ ((z, y) ↦ z ^ d * M β y)` is linearly independent. -/
theorem linearIndependent_pow_mul_monomial
    {σ κ : Type*} [Fintype κ] [DecidableEq κ] (q : ℕ)
    (exponent : κ → (σ →₀ ℕ)) (hexp : Function.Injective exponent) :
    LinearIndependent ℂ
      (fun c : κ × Fin (q + 1) => fun p : ℂ × (σ → ℂ) =>
        p.1 ^ (c.2 : ℕ) *
          MvPolynomial.eval p.2 (MvPolynomial.monomial (exponent c.1) (1 : ℂ))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a hsum
  have hpt : ∀ (z : ℂ) (y : σ → ℂ),
      ∑ c : κ × Fin (q + 1), a c * (z ^ (c.2 : ℕ) *
        MvPolynomial.eval y (MvPolynomial.monomial (exponent c.1) (1 : ℂ))) = 0 := by
    intro z y
    have := congrFun hsum (z, y)
    simpa [Pi.smul_apply, smul_eq_mul] using this
  -- Separate the variables: for fixed `y`, read off the coefficients in `z`.
  have hdeg : ∀ (y : σ → ℂ) (d : Fin (q + 1)),
      ∑ β : κ, a (β, d) *
        MvPolynomial.eval y (MvPolynomial.monomial (exponent β) (1 : ℂ)) = 0 := by
    intro y
    apply powerCoeffs_eq_zero_of_eval_eq_zero
    intro z
    rw [← hpt z y, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro d _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro β _
    ring
  -- For each degree, distinct monomials separate the remaining coefficients.
  intro c
  obtain ⟨β, d⟩ := c
  refine monomial_coeffs_eq_zero_of_eval_eq_zero exponent hexp
    (fun β => a (β, d)) ?_ β
  intro y
  rw [map_sum]
  have hy := hdeg y d
  rw [← hy]
  refine Finset.sum_congr rfl ?_
  intro β' _
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  ring

end

end GaloisForLFunctions.HTGeometry
