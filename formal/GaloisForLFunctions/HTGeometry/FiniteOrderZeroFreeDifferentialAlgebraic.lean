import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA

/-!
# Finite-order zero-free entire functions are differentially algebraic

Hadamard factorization identifies every zero-free entire function with a finite-order envelope as
the exponential of a polynomial.  This leaf records the exact differential-algebraic consequence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A zero-free entire function with a finite-order envelope is differentially algebraic. -/
theorem differentiallyAlgebraic_of_zeroFree_of_finiteOrderEnvelope {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : ∀ z, f z ≠ 0) (henv : FiniteOrderEnvelope f) :
    DifferentiallyAlgebraic f := by
  obtain ⟨p, hp⟩ := exists_polynomial_exp_of_ne_zero hf hne henv
  have hfun : f = fun z => Complex.exp (p.eval z) := funext hp
  rw [hfun]
  exact differentiallyAlgebraic_exp_polynomial p

/-- Consequently, no zero-free hypertranscendental entire function has finite order. -/
theorem not_finiteOrderEnvelope_of_zeroFree_of_hypertranscendental {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : ∀ z, f z ≠ 0) (hHT : Hypertranscendental f) :
    ¬ FiniteOrderEnvelope f :=
  fun henv => hHT (differentiallyAlgebraic_of_zeroFree_of_finiteOrderEnvelope hf hne henv)

end

end GaloisForLFunctions.HTGeometry
