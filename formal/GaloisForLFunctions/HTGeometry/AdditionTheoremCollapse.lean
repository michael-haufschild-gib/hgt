import GaloisForLFunctions.HTGeometry.AutonomousDifferentialAlgebraic

/-!
# An algebraic addition theorem forces differential algebraicity

If `f(x + y)` is a fixed two-variable polynomial in `f x` and `f y`, differentiating in `y` at the
origin gives a first-order autonomous equation `f' = Q(f)`, so `f` is differentially algebraic.
No classification of functions with addition theorems is needed.
-/

open Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- Two-variable evaluation of `P ∈ ℂ[u][v]`. -/
def biEval (P : Polynomial (Polynomial ℂ)) (u v : ℂ) : ℂ :=
  Polynomial.eval v (Polynomial.map (Polynomial.evalRingHom u) P)

theorem biEval_eq_eval_eval (P : Polynomial (Polynomial ℂ)) (u c : ℂ) :
    biEval P u c = Polynomial.eval u (Polynomial.eval (Polynomial.C c) P) := by
  rw [biEval]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
      rfl

/-- **An algebraic addition theorem forces a first-order autonomous equation.** -/
theorem deriv_eq_polynomial_of_additionTheorem {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {P : Polynomial (Polynomial ℂ)} (hadd : ∀ x y : ℂ, f (x + y) = biEval P (f x) (f y))
    (x : ℂ) :
    deriv f x
      = Polynomial.eval (f x)
          (Polynomial.C (deriv f 0) * Polynomial.eval (Polynomial.C (f 0))
            (Polynomial.derivative P)) := by
  have hfun : (fun y : ℂ => f (x + y)) = fun y : ℂ => biEval P (f x) (f y) :=
    funext fun y => hadd x y
  set R : Polynomial ℂ := Polynomial.map (Polynomial.evalRingHom (f x)) P with hR
  have hd1 : deriv (fun y : ℂ => f (x + y)) 0 = deriv f x := by
    simpa using deriv_comp_const_add f x 0
  have hd2 : deriv (fun y : ℂ => biEval P (f x) (f y)) 0
      = (Polynomial.derivative R).eval (f 0) * deriv f 0 := by
    have hcomp : (fun y : ℂ => biEval P (f x) (f y))
        = (fun w : ℂ => Polynomial.eval w R) ∘ f := rfl
    rw [hcomp, deriv_comp 0 (R.differentiable (f 0)) (hf 0), Polynomial.deriv]
  rw [← hd1, hfun, hd2, Polynomial.eval_mul, Polynomial.eval_C, ← biEval_eq_eval_eval, biEval,
    Polynomial.derivative_map]
  ring

theorem autonomousAnnihilator_of_additionTheorem {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {P : Polynomial (Polynomial ℂ)} (hadd : ∀ x y : ℂ, f (x + y) = biEval P (f x) (f y)) :
    AutonomousAnnihilator f 1
      (Polynomial.X - Polynomial.C
        ((Polynomial.C (deriv f 0) * Polynomial.eval (Polynomial.C (f 0))
            (Polynomial.derivative P)).eval₂ MvPolynomial.C
              (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ))) := by
  intro z
  have hkey := deriv_eq_polynomial_of_additionTheorem hf hadd z
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
  have hmv : ∀ Q : Polynomial ℂ,
      MvPolynomial.eval (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z)
        (Q.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin 1))) = Q.eval (f z) := by
    intro Q
    rw [Polynomial.hom_eval₂]
    have hC : (MvPolynomial.eval (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z)).comp
        (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 1) ℂ) = RingHom.id ℂ := by
      refine RingHom.ext fun c => ?_
      simp
    have hX : MvPolynomial.eval (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z)
        (MvPolynomial.X (0 : Fin 1)) = f z := by
      simp
    rw [hC, hX, Polynomial.eval₂_id]
  rw [hmv, iteratedDeriv_one, hkey, sub_self]

/-- **An algebraic addition theorem forces differential algebraicity.** -/
theorem differentiallyAlgebraic_of_additionTheorem {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {P : Polynomial (Polynomial ℂ)} (hadd : ∀ x y : ℂ, f (x + y) = biEval P (f x) (f y)) :
    DifferentiallyAlgebraic f := by
  refine differentiallyAlgebraic_of_autonomous ?_ (autonomousAnnihilator_of_additionTheorem hf hadd)
  intro h0
  have hdeg := congrArg Polynomial.natDegree h0
  rw [Polynomial.natDegree_zero] at hdeg
  rw [Polynomial.natDegree_X_sub_C] at hdeg
  exact one_ne_zero hdeg

/-- **No hypertranscendental function has an algebraic addition theorem.** -/
theorem not_additionTheorem_of_hypertranscendental {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hHT : Hypertranscendental f) :
    ¬ ∃ P : Polynomial (Polynomial ℂ), ∀ x y : ℂ, f (x + y) = biEval P (f x) (f y) := by
  rintro ⟨P, hadd⟩
  exact hHT (differentiallyAlgebraic_of_additionTheorem hf hadd)

end

end GaloisForLFunctions
