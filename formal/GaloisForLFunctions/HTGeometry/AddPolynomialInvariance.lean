import GaloisForLFunctions.HTGeometry.AxisShiftSubstitution

/-!
# Adding a polynomial preserves hypertranscendence

The jets of `f + p` for a polynomial `p` are the jets of `f` shifted slot by slot by the successive
derivatives of `p`, each a polynomial in the spectral variable.  That is exactly the axis shift, so
a differential relation for `f + p` transfers to one for `f`.

This is the additive half of the rational gauge; the multiplicative half is genuinely different, as
its inverse leaves the polynomial ring.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Evaluating a univariate polynomial substituted at one variable. -/
theorem eval_aeval_X {σ : Type*} (i : σ) (q : Polynomial ℂ) (v : σ → ℂ) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X i) q)
      = Polynomial.eval (v i) q := by
  induction q using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial k a ih => simp

/-- Evaluating an axis-shifted polynomial is evaluating the original at the shifted point. -/
theorem eval_axisShiftSubst {σ : Type*} [DecidableEq σ] (i : σ) (h : σ → Polynomial ℂ)
    (Q : MvPolynomial σ ℂ) (v : σ → ℂ) :
    MvPolynomial.eval v (axisShiftSubst i h Q)
      = MvPolynomial.eval
          (fun s => if s = i then v i else v s + Polynomial.aeval (v i) (h s)) Q := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [axisShiftSubst]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p s hp =>
      rw [map_mul, map_mul, hp]
      by_cases hs : s = i
      · subst hs
        simp [axisShiftSubst]
      · simp [axisShiftSubst, hs, eval_aeval_X]

/-- The iterated derivatives of a polynomial function are the polynomial's iterated derivatives. -/
theorem iteratedDeriv_polynomial_eval (p : Polynomial ℂ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun w => Polynomial.eval w p) z
      = Polynomial.eval z (Polynomial.derivative^[j] p) := by
  induction j generalizing p with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun w => Polynomial.eval w p)
          = fun w => Polynomial.eval w (Polynomial.derivative p) := by
        funext w
        exact Polynomial.deriv p
      rw [hderiv, ih, Function.iterate_succ_apply]

/-- The jets of a smooth function shifted by a polynomial.  Differentiability is genuinely needed:
unlike a constant shift, adding a polynomial requires the derivative of a sum to split. -/
theorem iteratedDeriv_add_polynomial (f : ℂ → ℂ)
    (hf : ∀ j, Differentiable ℂ (iteratedDeriv j f)) (b : Polynomial ℂ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun w => f w + Polynomial.eval w b) z
      = iteratedDeriv j f z + Polynomial.eval z (Polynomial.derivative^[j] b) := by
  induction j generalizing f b with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hderiv : deriv (fun w => f w + Polynomial.eval w b)
          = fun w => deriv f w + Polynomial.eval w (Polynomial.derivative b) := by
        funext w
        have hf0 : DifferentiableAt ℂ f w := by
          have h0 := hf 0
          rw [iteratedDeriv_zero] at h0
          exact h0.differentiableAt
        have h2 : HasDerivAt (fun x => Polynomial.eval x b)
            (Polynomial.eval w (Polynomial.derivative b)) w := b.hasDerivAt w
        exact (hf0.hasDerivAt.add h2).deriv
      rw [hderiv]
      have hfd : ∀ k, Differentiable ℂ (iteratedDeriv k (deriv f)) := by
        intro k
        have : iteratedDeriv k (deriv f) = iteratedDeriv (k + 1) f := by
          rw [iteratedDeriv_succ']
        rw [this]
        exact hf (k + 1)
      rw [ih (deriv f) hfd (Polynomial.derivative b), Function.iterate_succ_apply]

/-- **Adding a polynomial preserves differential algebraicity.** -/
theorem differentiallyAlgebraic_add_polynomial {f : ℂ → ℂ}
    (hf : ∀ j, Differentiable ℂ (iteratedDeriv j f)) (b : Polynomial ℂ)
    (h : DifferentiallyAlgebraic fun w => f w + Polynomial.eval w b) :
    DifferentiallyAlgebraic f := by
  classical
  obtain ⟨n, P, hP, hzero⟩ := h
  refine ⟨n, axisShiftSubst 0 (fun s : Fin (n + 2) => Polynomial.derivative^[s.1 - 1] b) P,
    axisShiftSubst_ne_zero 0 _ hP, ?_⟩
  intro z
  rw [eval_axisShiftSubst]
  have hjet : (fun s : Fin (n + 2) =>
      if s = 0 then (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
          Fin (n + 2) → ℂ) 0
        else (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
          Fin (n + 2) → ℂ) s
          + Polynomial.aeval
              ((Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
                Fin (n + 2) → ℂ) 0)
              (Polynomial.derivative^[s.1 - 1] b))
      = Fin.cons z (fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ) (fun w => f w + Polynomial.eval w b) z) := by
    funext s
    rcases Fin.eq_zero_or_eq_succ s with hs | ⟨s', hs⟩
    · subst hs
      simp
    · subst hs
      rw [if_neg (Fin.succ_ne_zero s')]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Nat.add_sub_cancel]
      rw [iteratedDeriv_add_polynomial f hf b]
      simp
  rw [hjet]
  exact hzero z

end

end GaloisForLFunctions.HTGeometry
