import GaloisForLFunctions.HTGeometry.CascadeExpression

/-!
# Polynomials in the states with polynomial coefficients

A relation among the cascade states is a multivariate polynomial in them whose coefficients are
polynomials in `z`.  Packaging it as `MvPolynomial (Fin n) (Polynomial ℂ)` lets mathlib's ring
structure carry the sums and products, so the expansion into monomials — the form
`PolyIndependent` speaks about — is a `Finset` fact rather than a hand-rolled convolution.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- The function defined by a polynomial in the states with polynomial coefficients. -/
noncomputable def statePoly (F : Fin n → ℂ → ℂ) (P : MvPolynomial (Fin n) (Polynomial ℂ)) :
    ℂ → ℂ :=
  fun z => MvPolynomial.eval (fun i => F i z)
    (MvPolynomial.map (Polynomial.evalRingHom z) P)

@[simp] theorem statePoly_apply (F : Fin n → ℂ → ℂ) (P : MvPolynomial (Fin n) (Polynomial ℂ))
    (z : ℂ) :
    statePoly F P z
      = MvPolynomial.eval (fun i => F i z) (MvPolynomial.map (Polynomial.evalRingHom z) P) := rfl

@[simp] theorem statePoly_zero (F : Fin n → ℂ → ℂ) : statePoly F 0 = fun _ => 0 := by
  funext z
  simp [statePoly]

@[simp] theorem statePoly_C (F : Fin n → ℂ → ℂ) (p : Polynomial ℂ) :
    statePoly F (MvPolynomial.C p) = fun z => p.eval z := by
  funext z
  simp [statePoly]

@[simp] theorem statePoly_X (F : Fin n → ℂ → ℂ) (i : Fin n) :
    statePoly F (MvPolynomial.X i) = F i := by
  funext z
  simp [statePoly]

theorem statePoly_add (F : Fin n → ℂ → ℂ) (P Q : MvPolynomial (Fin n) (Polynomial ℂ)) :
    statePoly F (P + Q) = fun z => statePoly F P z + statePoly F Q z := by
  funext z
  simp [statePoly]

theorem statePoly_mul (F : Fin n → ℂ → ℂ) (P Q : MvPolynomial (Fin n) (Polynomial ℂ)) :
    statePoly F (P * Q) = fun z => statePoly F P z * statePoly F Q z := by
  funext z
  simp [statePoly]

/-- **The monomial expansion.**  The function defined by a polynomial in the states is the monomial
sum `PolyIndependent` speaks about, indexed by the support of the specialised polynomial. -/
theorem statePoly_eq_sum (F : Fin n → ℂ → ℂ) (P : MvPolynomial (Fin n) (Polynomial ℂ)) (z : ℂ) :
    statePoly F P z
      = ∑ e ∈ (MvPolynomial.map (Polynomial.evalRingHom z) P).support,
          (MvPolynomial.coeff e P).eval z * ∏ i, (F i z) ^ (e i) := by
  rw [statePoly, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [MvPolynomial.coeff_map]
  rfl

/-- The monomial expansion indexed by the polynomial's own support: the terms killed by
specialisation contribute nothing. -/
theorem statePoly_eq_sum_support (F : Fin n → ℂ → ℂ)
    (P : MvPolynomial (Fin n) (Polynomial ℂ)) (z : ℂ) :
    statePoly F P z
      = ∑ e ∈ P.support, (MvPolynomial.coeff e P).eval z * ∏ i, (F i z) ^ (e i) := by
  classical
  rw [statePoly_eq_sum]
  refine Finset.sum_subset (MvPolynomial.support_map_subset _ P) ?_
  intro e _ hnot
  have hzero : MvPolynomial.coeff e (MvPolynomial.map (Polynomial.evalRingHom z) P) = 0 := by
    by_contra hc
    exact hnot (MvPolynomial.mem_support_iff.mpr hc)
  rw [MvPolynomial.coeff_map] at hzero
  rw [show (MvPolynomial.coeff e P).eval z = 0 from hzero, zero_mul]

/-- **Polynomial independence says exactly that no nonzero polynomial in the states vanishes.** -/
theorem eq_zero_of_polyIndependent {F : Fin n → ℂ → ℂ} (h : PolyIndependent F)
    {P : MvPolynomial (Fin n) (Polynomial ℂ)} (hP : ∀ z : ℂ, statePoly F P z = 0) : P = 0 := by
  classical
  have hsum : ∀ w : ℂ, ∑ e ∈ P.support,
      (MvPolynomial.coeff e P).eval w * ∏ i, (F i w) ^ (e i) = 0 := by
    intro w
    rw [← statePoly_eq_sum_support]
    exact hP w
  have hcoeff := h P.support (fun e => e) (fun e => MvPolynomial.coeff e P)
    (DFunLike.coe_injective.injOn) hsum
  by_contra hne
  obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.mp hne
  exact he (hcoeff e (MvPolynomial.mem_support_iff.mpr he))

end GaloisForLFunctions.HTGeometry
