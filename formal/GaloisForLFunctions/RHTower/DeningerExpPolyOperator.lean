import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The Euler operator of an exponential polynomial

Substituting `X = e^{-δ s}` turns a polynomial into an exponential polynomial, and differentiating
in `s` corresponds to the Euler operator `𝒟 = -δ X d/dX` on the polynomial side.  Iterating gives
every derivative of the exponential polynomial as an evaluation of an iterated Euler operator, so
the jets of an exponential polynomial are polynomial data.

* `deningerEulerOp` : the operator `𝒟`.
* `deningerExpComposite_deriv` : one derivative.
* `deningerExpComposite_iteratedDeriv` : every derivative.
-/

namespace RHTower

open Polynomial

section EulerOperator

/-- The Euler operator `𝒟 P = -δ X P'`, the polynomial shadow of differentiating in `s` after the
substitution `X = e^{-δ s}`. -/
noncomputable def deningerEulerOp (δ : ℂ) (P : ℂ[X]) : ℂ[X] :=
  -(C δ) * X * derivative P

theorem deningerEulerOp_eval (δ : ℂ) (P : ℂ[X]) (w : ℂ) :
    (deningerEulerOp δ P).eval w = -δ * w * (derivative P).eval w := by
  rw [deningerEulerOp]
  simp

/-- The exponential substitution is differentiable, with the Euler operator as its derivative. -/
theorem deningerExpComposite_hasDerivAt (δ : ℂ) (P : ℂ[X]) (s : ℂ) :
    HasDerivAt (fun z => P.eval (Complex.exp (-δ * z)))
      ((deningerEulerOp δ P).eval (Complex.exp (-δ * s))) s := by
  have hlin : HasDerivAt (fun z : ℂ => -δ * z) (-δ) s := by
    simpa using (hasDerivAt_id s).const_mul (-δ)
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-δ * z))
      (Complex.exp (-δ * s) * (-δ)) s := hlin.cexp
  have hpoly : HasDerivAt (fun w : ℂ => P.eval w)
      ((derivative P).eval (Complex.exp (-δ * s))) (Complex.exp (-δ * s)) :=
    Polynomial.hasDerivAt P _
  have hcomp := hpoly.comp s hexp
  have hval : (derivative P).eval (Complex.exp (-δ * s)) * (Complex.exp (-δ * s) * (-δ))
      = -δ * Complex.exp (-δ * s) * (derivative P).eval (Complex.exp (-δ * s)) := by ring
  rw [deningerEulerOp_eval, ← hval]
  exact hcomp

theorem deningerExpComposite_deriv (δ : ℂ) (P : ℂ[X]) (s : ℂ) :
    deriv (fun z => P.eval (Complex.exp (-δ * z))) s
      = (deningerEulerOp δ P).eval (Complex.exp (-δ * s)) :=
  (deningerExpComposite_hasDerivAt δ P s).deriv

/-- **Every derivative of an exponential polynomial** is the corresponding iterate of the Euler
operator, evaluated at the exponential substitution. -/
theorem deningerExpComposite_iteratedDeriv (δ : ℂ) (P : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z => P.eval (Complex.exp (-δ * z)))
      = fun s => ((deningerEulerOp δ)^[k] P).eval (Complex.exp (-δ * s)) := by
  induction k with
  | zero =>
    funext s
    rw [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [Function.iterate_succ_apply']
    exact deningerExpComposite_deriv δ ((deningerEulerOp δ)^[k] P) s

end EulerOperator

end RHTower
