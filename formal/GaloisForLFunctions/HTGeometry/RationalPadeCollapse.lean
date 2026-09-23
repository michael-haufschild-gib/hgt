import GaloisForLFunctions.HTGeometry.AdditionTheoremCollapse
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Rational representations and a stabilizing Padé table force differential algebraicity

A function satisfying `Q(z)·f(z) = P(z)` with `Q ≠ 0` satisfies an order-zero algebraic
differential equation.  A Padé table that stabilizes gives exactly such a representation: the
approximant error has vanishing jets of every order at the origin, so for an entire function it
vanishes identically.
-/

open Polynomial

namespace GaloisForLFunctions

noncomputable section

theorem eval_aeval_X0_rationalPadeCollapse (P : Polynomial ℂ) (g : Fin 2 → ℂ) :
    MvPolynomial.eval g (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) P)
      = P.eval (g 0) := by
  induction P using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp

/-- **A rational representation forces differential algebraicity.** -/
theorem differentiallyAlgebraic_of_rational {f : ℂ → ℂ} (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hrep : ∀ z : ℂ, Q.eval z * f z = P.eval z) : DifferentiallyAlgebraic f := by
  classical
  refine ⟨0, Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) Q * MvPolynomial.X 1
      - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) P, ?_, ?_⟩
  · intro h0
    refine hQ (Polynomial.funext fun v => ?_)
    have h1 := congrArg (MvPolynomial.eval ![v, (1 : ℂ)]) h0
    have h2 := congrArg (MvPolynomial.eval ![v, (0 : ℂ)]) h0
    rw [map_sub, map_mul, eval_aeval_X0_rationalPadeCollapse, eval_aeval_X0_rationalPadeCollapse, MvPolynomial.eval_X, map_zero] at h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
    rw [Polynomial.eval_zero]
    linear_combination h1 - h2
  · intro z
    have h0 : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z) : Fin 2 → ℂ) 0 = z := by
      simp
    have h1 : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z) : Fin 2 → ℂ) 1 = f z := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_zero]
    rw [map_sub, map_mul, eval_aeval_X0_rationalPadeCollapse, eval_aeval_X0_rationalPadeCollapse, MvPolynomial.eval_X, h0, h1, hrep z,
      sub_self]

/-- An entire function all of whose jets vanish at the origin is identically zero. -/
theorem eq_zero_of_iteratedDeriv_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hjet : ∀ k : ℕ, iteratedDeriv k g 0 = 0) (z : ℂ) : g z = 0 := by
  have h := Complex.hasSum_taylorSeries_of_entire hg 0 z
  have hz : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ • (z - 0) ^ n • iteratedDeriv n g 0 = 0 := by
    intro n
    rw [hjet n, smul_zero, smul_zero]
  rw [show (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (z - 0) ^ n • iteratedDeriv n g 0)
      = fun _ => 0 from funext hz] at h
  exact (hasSum_zero.unique h).symm

/-- **A stabilizing Padé table forces differential algebraicity.**  If the approximation error of a
fixed pair `(P, Q)` has vanishing jets of every order at the origin, the representation is exact and
`f` satisfies an order-zero algebraic differential equation. -/
theorem differentiallyAlgebraic_of_padeStabilization {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hjet : ∀ k : ℕ, iteratedDeriv k (fun z => Q.eval z * f z - P.eval z) 0 = 0) :
    DifferentiallyAlgebraic f := by
  refine differentiallyAlgebraic_of_rational P Q hQ fun z => ?_
  have hdiff : Differentiable ℂ (fun z : ℂ => Q.eval z * f z - P.eval z) :=
    (Q.differentiable.mul hf).sub P.differentiable
  exact sub_eq_zero.1 (eq_zero_of_iteratedDeriv_zero hdiff hjet z)

end

end GaloisForLFunctions
