import GaloisForLFunctions.HTGeometry.PolynomialEulerJet
import GaloisForLFunctions.HTGeometry.PencilIteratedDerivation
import GaloisForLFunctions.HTGeometry.PencilDirectionalDerivation

/-!
# Jets of a source along an exponential phase

Composing a source with `t ↦ exp (λ t + c)` turns the derivation `d/dt` into `λ` times the Euler
operator on the source:

```text
d^r/dt^r [ Ψ (exp (λ t + c)) ] = λ^r · (Θ^r Ψ) (exp (λ t + c)).
```

This is the one-variable form of the pencil identity `D_w^r (Ψ ∘ exp ∘ L) = (L w)^r · Θ^r Ψ ∘ exp ∘ L`,
with the affine shift `c` absorbing the translation of the orbit.  For a polynomial source the Euler
operator is the polynomial Euler operator, so the jets of the carrier are exactly the Euler jets of
the coefficient window.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The Euler operator computes the jets along an exponential phase.** -/
theorem iteratedDeriv_expComp {Ψ : ℂ → ℂ} (hΨ : ContDiff ℂ (⊤ : ℕ∞) Ψ) (lam c : ℂ) (r : ℕ) :
    ∀ t : ℂ, iteratedDeriv r (fun s => Ψ (Complex.exp (lam * s + c))) t =
      lam ^ r * (eulerOp^[r] Ψ) (Complex.exp (lam * t + c)) := by
  induction r generalizing Ψ with
  | zero => intro t; simp
  | succ r ih =>
      have hderiv : deriv (fun s => Ψ (Complex.exp (lam * s + c))) =
          fun s => lam * (eulerOp Ψ) (Complex.exp (lam * s + c)) := by
        funext s
        have h1 : HasDerivAt (fun u : ℂ => lam * u + c) lam s := by
          simpa using ((hasDerivAt_id s).const_mul lam).add_const c
        have hE : HasDerivAt (fun u : ℂ => Complex.exp (lam * u + c))
            (Complex.exp (lam * s + c) * lam) s := h1.cexp
        have hΨd : HasDerivAt Ψ (deriv Ψ (Complex.exp (lam * s + c)))
            (Complex.exp (lam * s + c)) :=
          ((hΨ.differentiable (by simp)).differentiableAt).hasDerivAt
        have hcomp : HasDerivAt (fun u : ℂ => Ψ (Complex.exp (lam * u + c)))
            (deriv Ψ (Complex.exp (lam * s + c)) * (Complex.exp (lam * s + c) * lam)) s :=
          hΨd.comp s hE
        rw [hcomp.deriv]
        show deriv Ψ (Complex.exp (lam * s + c)) * (Complex.exp (lam * s + c) * lam) =
          lam * (Complex.exp (lam * s + c) * deriv Ψ (Complex.exp (lam * s + c)))
        ring
      have hg : ContDiff ℂ (⊤ : ℕ∞) (fun u : ℂ => (eulerOp Ψ) (Complex.exp (lam * u + c))) :=
        (contDiff_eulerOp hΨ).comp (Complex.contDiff_exp.comp
          ((contDiff_const.mul contDiff_id).add contDiff_const))
      intro t
      rw [iteratedDeriv_succ', hderiv, iteratedDeriv_const_mul' hg lam r]
      show lam * iteratedDeriv r (fun u : ℂ => (eulerOp Ψ) (Complex.exp (lam * u + c))) t = _
      rw [ih (contDiff_eulerOp hΨ) t, Function.iterate_succ_apply]
      ring

/-- The analytic Euler operator on a polynomial is the polynomial Euler operator. -/
theorem eulerOp_iterate_polynomial (p : Polynomial ℂ) (r : ℕ) :
    eulerOp^[r] (fun u => Polynomial.eval u p) = fun u => Polynomial.eval u (polyEuler^[r] p) := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [show eulerOp (fun u => Polynomial.eval u p)
          = fun u => Polynomial.eval u (polyEuler p) by
        funext u
        rw [eulerOp, polyEuler, Polynomial.deriv, Polynomial.eval_mul, Polynomial.eval_X]]
      exact ih (polyEuler p)

/-- **The jets of a polynomial carrier along an exponential phase are its Euler jets.** -/
theorem iteratedDeriv_expComp_polynomial (p : Polynomial ℂ) (lam c : ℂ) (r : ℕ) (t : ℂ) :
    iteratedDeriv r (fun s => Polynomial.eval (Complex.exp (lam * s + c)) p) t =
      lam ^ r * Polynomial.eval (Complex.exp (lam * t + c)) (polyEuler^[r] p) := by
  have hcd : ContDiff ℂ (⊤ : ℕ∞) (fun u => Polynomial.eval u p) := by
    have := Polynomial.contDiff_aeval (𝕜 := ℂ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (f := p)
    simpa using this
  rw [iteratedDeriv_expComp hcd lam c r t, eulerOp_iterate_polynomial p r]

end

end GaloisForLFunctions.HTGeometry
