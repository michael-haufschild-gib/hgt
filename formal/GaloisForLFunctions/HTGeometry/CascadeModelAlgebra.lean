import GaloisForLFunctions.HTGeometry.PolynomialCascadeModel

/-!
# Cascades modelled by an arbitrary differential algebra

A family of entire functions whose derivative law is *algebraic* rather than polynomial in the
family is modelled by a derivation on a commutative `ℂ`-algebra together with a pointwise
evaluation into `ℂ` that turns the model derivation into complex differentiation.  Every jet of the
realized function is then the evaluation of a model jet, so independence of the model jets forbids
every algebraic differential equation of lower order.

This is the algebra-valued form of `PolynomialCascadeModel`; the polynomial model is the case
`R = MvPolynomial ℕ ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- An analytic realization of a differential `ℂ`-algebra: a family of `ℂ`-algebra evaluations
whose variation in the base point is the model derivation. -/
structure DifferentialRealization (R : Type*) [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) where
  /-- Evaluation of the model at a base point. -/
  ev : ℂ → (R →ₐ[ℂ] ℂ)
  /-- Moving the base point differentiates by the model derivation. -/
  deriv_ev : ∀ (x : R) (z : ℂ), deriv (fun w => ev w x) z = ev z (δ x)

namespace DifferentialRealization

variable {R : Type*} [CommRing R] [Algebra ℂ R] {δ : Derivation ℂ R R}

/-- The realized function attached to a model element. -/
def fn (E : DifferentialRealization R δ) (x : R) : ℂ → ℂ := fun w => E.ev w x

/-- **The analytic jets are the model jets.** -/
theorem ev_jet (E : DifferentialRealization R δ) (x : R) (i : ℕ) :
    iteratedDeriv i (E.fn x) = E.fn (((δ : R → R)^[i]) x) := by
  induction i with
  | zero => rw [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ i ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      funext z
      exact E.deriv_ev _ z

/-- **No low-order equation from independent model jets.**  If the coordinate element `c`
realizes the identity, nonzero model elements do not vanish identically, and the coordinate
together with the first `m + 1` model jets of `x` are algebraically independent over `ℂ`, then the
realized function satisfies no algebraic differential equation of order `m`. -/
theorem not_differentiallyAlgebraicOfOrder_of_realization
    (E : DifferentialRealization R δ) {m : ℕ} (c x : R)
    (hc : ∀ z : ℂ, E.ev z c = z)
    (hind : ∀ Q : R, Q ≠ 0 → ∃ z : ℂ, E.ev z Q ≠ 0)
    (hjet : AlgebraicIndependent ℂ
      (Fin.cons c (fun j : Fin (m + 1) => ((δ : R → R)^[(j : ℕ)]) x) : Fin (m + 2) → R)) :
    ¬ DifferentiallyAlgebraicOfOrder (E.fn x) m := by
  rintro ⟨P, hP0, hPz⟩
  set v : Fin (m + 2) → R :=
    Fin.cons c (fun j : Fin (m + 1) => ((δ : R → R)^[(j : ℕ)]) x) with hv
  have hQ0 : MvPolynomial.aeval v P ≠ 0 := by
    intro h0
    exact hP0 (hjet (by rw [h0, map_zero]))
  obtain ⟨z, hz⟩ := hind _ hQ0
  refine hz ?_
  have hcomp : ((E.ev z).toRingHom).comp
        (MvPolynomial.aeval v : MvPolynomial (Fin (m + 2)) ℂ →ₐ[ℂ] R).toRingHom
      = (MvPolynomial.eval (fun i => E.ev z (v i)) :
          MvPolynomial (Fin (m + 2)) ℂ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show E.ev z (MvPolynomial.aeval v (MvPolynomial.C a)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.eval_C]
      exact (E.ev z).commutes a
    · intro i
      show E.ev z (MvPolynomial.aeval v (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
  have hval : E.ev z (MvPolynomial.aeval v P)
      = MvPolynomial.eval (fun i => E.ev z (v i)) P := RingHom.congr_fun hcomp P
  rw [hval]
  have hvec : (fun i : Fin (m + 2) => E.ev z (v i))
      = Fin.cons z (fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) (E.fn x) z) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rw [hv, Fin.cons_zero, Fin.cons_zero, hc]
    · intro j
      rw [hv, Fin.cons_succ, Fin.cons_succ, E.ev_jet x (j : ℕ)]
      rfl
  rw [hvec]
  exact hPz z

end DifferentialRealization

end GaloisForLFunctions.HTGeometry
