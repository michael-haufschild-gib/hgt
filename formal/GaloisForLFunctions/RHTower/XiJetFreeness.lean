import GaloisForLFunctions.HTGeometry.DifferentialOrder
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation
import GaloisForLFunctions.HTGeometry.HypertranscendentalPointJetFreeness
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional

/-!
# Free derivative jets of the completed xi function

This leaf instantiates the generic jet consequences of function hypertranscendence with the
unconditional theorem for the completed Riemann xi function.  It records algebraic independence of
the derivative functions, algebraic independence after adjoining the point coordinate, isolation of
every nonzero differential-polynomial relation locus, and failure of differential algebraicity at
each finite order.

These are global function-theoretic consequences of xi hypertranscendence.  They contain no
zero-location or Riemann-hypothesis conclusion.
-/

namespace RHTower

open GaloisForLFunctions

/-- Every finite initial family of completed-xi derivative functions is algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_xi_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi) :=
  xi_hypertranscendental.algebraicIndependent_initialJets n

/-- **Completed-xi free jets.** All derivative functions of xi are algebraically independent over
`ℂ`. -/
theorem algebraicIndependent_xi_iteratedDeriv :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j xi) :=
  xi_hypertranscendental.algebraicIndependent_iteratedDeriv

/-- The point coordinate together with every finite initial completed-xi derivative jet is
algebraically independent over `ℂ`. -/
theorem algebraicIndependent_xi_pointInitialJets (n : ℕ) :
    AlgebraicIndependent ℂ (pointJetFunctionTuple xi n) :=
  xi_hypertranscendental.algebraicIndependent_pointInitialJets n

/-- Every nonzero differential polynomial has an isolated vanishing locus on the completed-xi
jets. -/
theorem xi_jetEval_isolated {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    ∀ z₀, ¬ (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi z) P = 0) :=
  xi_hypertranscendental.jetEval_isolated xi_differentiable hP

/-- The completed xi function satisfies no algebraic differential equation of any prescribed
finite order. -/
theorem xi_not_differentiallyAlgebraicOfOrder (n : ℕ) :
    ¬ DifferentiallyAlgebraicOfOrder xi n :=
  xi_hypertranscendental.not_differentiallyAlgebraicOfOrder n

end RHTower
