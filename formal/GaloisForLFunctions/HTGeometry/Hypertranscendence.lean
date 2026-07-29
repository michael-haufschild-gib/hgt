import Mathlib

/-!
# Hypertranscendence: the founding notion of the branch

Hölder's 1887 theorem is that `Γ` satisfies no *algebraic differential equation* — it is
hypertranscendental.  This file gives that notion a formal home (absent from mathlib and from this
tree): a function is **differentially algebraic** when some nonzero polynomial in the variable `s`, the
function, and its derivatives vanishes identically, and **hypertranscendental** when it is not.

The differential polynomial is a genuine polynomial in `s, f, f', …, f⁽ⁿ⁾` — the variable `s` is a jet
coordinate (index `0`), matching the classical statement (an algebraic differential equation has
polynomial coefficients in `s`).

* `DifferentiallyAlgebraic` / `Hypertranscendental` — the definitions.
* `differentiallyAlgebraic_of_algebraic` — an algebraic function (root of a nonzero polynomial) is
  differentially algebraic (an order-`0` differential relation).  Hence
  `hypertranscendental_imp_transcendental`: a hypertranscendental function is transcendental — the
  "hyper" strictly strengthens "transcendental", justifying the name.
* `differentiallyAlgebraic_exp` — the exponential is differentially algebraic (`y' − y = 0`): the
  notion is non-vacuous.  `Hypertranscendental Complex.Gamma` (Hölder) is the frontier statement it
  sets up.
-/

open scoped BigOperators

namespace GaloisForLFunctions

/-- **Differentially algebraic.**  `f : ℂ → ℂ` satisfies an algebraic differential equation: there is
an order `n` and a nonzero polynomial `P` in the `n+2` jet variables `(s, y₀, …, yₙ)` with
`P(s, f, f', …, f⁽ⁿ⁾) ≡ 0`.  Jet variable `0` is the point `s`; variable `j+1` is `f⁽ʲ⁾`. -/
def DifferentiallyAlgebraic (f : ℂ → ℂ) : Prop :=
  ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
    ∀ z : ℂ, MvPolynomial.eval (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) P = 0

/-- **Hypertranscendental.**  `f` satisfies no algebraic differential equation. -/
def Hypertranscendental (f : ℂ → ℂ) : Prop := ¬ DifferentiallyAlgebraic f

/-- Evaluating the embedding `X₁ ↦` (the value slot `f`) of a univariate polynomial recovers the
univariate value at the slot-`1` coordinate. -/
theorem eval_aeval_X1 (P : Polynomial ℂ) (g : Fin 2 → ℂ) :
    MvPolynomial.eval g (Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) P)
      = P.eval (g 1) := by
  induction P using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp

/-- **An algebraic function is differentially algebraic.**  If a nonzero univariate polynomial `P`
vanishes on `f` (`P(f z) = 0` for all `z`), then `f` satisfies the order-`0` differential relation
`P(y₀) = 0`, so it is differentially algebraic. -/
theorem differentiallyAlgebraic_of_algebraic {f : ℂ → ℂ} (P : Polynomial ℂ) (hP : P ≠ 0)
    (hroot : ∀ z, P.eval (f z) = 0) : DifferentiallyAlgebraic f := by
  refine ⟨0, Polynomial.aeval (MvPolynomial.X 1) P, ?_, ?_⟩
  · intro h
    apply hP
    apply Polynomial.funext
    intro v
    have hv := eval_aeval_X1 P (fun i => if i = 1 then v else 0)
    rw [h] at hv
    simpa using hv.symm
  · intro z
    rw [eval_aeval_X1]
    have : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z) : Fin 2 → ℂ) 1 = f z := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_zero]
    rw [this]; exact hroot z

/-- **Hypertranscendental ⟹ transcendental.**  A hypertranscendental function is transcendental as a
function: it is the root of no nonzero univariate polynomial.  The "hyper" strictly strengthens
"transcendental". -/
theorem hypertranscendental_imp_transcendental {f : ℂ → ℂ} (hf : Hypertranscendental f) :
    ¬ ∃ P : Polynomial ℂ, P ≠ 0 ∧ ∀ z, P.eval (f z) = 0 := by
  rintro ⟨P, hP, hroot⟩
  exact hf (differentiallyAlgebraic_of_algebraic P hP hroot)

/-- **Every exponential `s ↦ exp(c·s)` is differentially algebraic** (`y' − c·y = 0`).  Witness
`P = X₂ − c·X₁` at order `1`, using `d/ds exp(c·s) = c·exp(c·s)`.  In particular the class contains all
solutions of a linear constant-coefficient first-order ODE — and hence, via a change of variable, each
shifted exponential monomial `exp(−s·log(n+a))`. -/
theorem differentiallyAlgebraic_cexp_linear (c : ℂ) :
    DifferentiallyAlgebraic (fun s => Complex.exp (c * s)) := by
  refine ⟨1, MvPolynomial.X 2 - MvPolynomial.C c * MvPolynomial.X 1, ?_, ?_⟩
  · intro h
    have hco := congrArg (MvPolynomial.coeff (Finsupp.single 2 1)) h
    simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_C_mul,
      Finsupp.single_eq_single_iff] at hco
  · intro z
    have hderiv : deriv (fun s => Complex.exp (c * s)) z = c * Complex.exp (c * z) := by
      have h1 : HasDerivAt (fun s : ℂ => c * s) c z := by simpa using (hasDerivAt_id z).const_mul c
      rw [h1.cexp.deriv]; ring
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [show (2 : Fin 3) = Fin.succ 1 from rfl, show (1 : Fin 3) = Fin.succ 0 from rfl,
      Fin.cons_succ, Fin.cons_succ]
    simp only [Fin.val_one, Fin.val_zero, iteratedDeriv_one, iteratedDeriv_zero, hderiv]
    ring

/-- **The exponential is differentially algebraic** (`y' − y = 0`): the notion is non-vacuous.
`Hypertranscendental Complex.Gamma` (Hölder) is the frontier statement it sets up. -/
theorem differentiallyAlgebraic_exp : DifferentiallyAlgebraic Complex.exp := by
  simpa only [one_mul] using differentiallyAlgebraic_cexp_linear 1

end GaloisForLFunctions
