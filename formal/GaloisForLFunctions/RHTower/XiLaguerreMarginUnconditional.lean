import GaloisForLFunctions.RHTower.XiLaguerrePolya

/-!
# The unconditional first-Laguerre falsification criterion for Xi

The Laguerre detector was stated relative to Pólya's interface
`RiemannHypothesis → LaguerrePolya Xi`.  That interface is a theorem, so the detector is
unconditional: one real point at which the first Laguerre inequality strictly fails refutes the
Riemann hypothesis, and consequently the inequality holds everywhere if the hypothesis does.
-/

namespace RHTower

noncomputable section

/-- **Unconditional Laguerre falsification.**  A single real `t` with
`(Ξ'(t))² < Ξ(t)·Ξ''(t)` refutes RH, with no interface hypothesis. -/
theorem laguerre_margin_neg_not_riemannHypothesis
    (h : ∃ t : ℝ, (deriv Xi t) ^ (2 : ℕ) < Xi t * deriv (deriv Xi) t) :
    ¬ RiemannHypothesis :=
  laguerre_margin_neg_not_RH_of_polya xi_laguerrePolya_of_rh h

/-- Contrapositive: RH forces the first Laguerre inequality at every real point. -/
theorem laguerre_inequality_Xi_of_riemannHypothesis (hRH : RiemannHypothesis) (t : ℝ) :
    Xi t * deriv (deriv Xi) t ≤ (deriv Xi t) ^ (2 : ℕ) :=
  laguerre_inequality_lp (xi_laguerrePolya_of_rh hRH) t

end

end RHTower
