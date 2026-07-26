import GaloisForLFunctions.RHTower.MobiusHalfDecayFromSubpower
import GaloisForLFunctions.RHTower.MobiusLaplaceBoundaryMultiplicity

/-!
# A coefficient criterion for the Riemann hypothesis

Composing the two previous steps removes every analytic hypothesis from the Möbius--Laplace
criterion.  A subpower bound on the Hermitian mixed convolution coefficients of the Möbius sequence,

```
Re R_k(N) ≤ C (N+1)^α    with   α + 1 ≤ k,
```

gives the half-power source decay, which the corpus criterion converts into the Riemann hypothesis
together with simplicity of the Xi divisor.

Contrapositively, a failure of the Riemann hypothesis forbids every such bound: the coefficient
order of the `2k`-fold Hermitian convolution must then exceed `k - 1`.  That is the no-go direction
of the raw-Möbius order law, with the corpus criterion standing in for the Mellin contradiction
against a single zero.
-/

namespace RHTower

/-- **Coefficient criterion.**  A subpower bound on the Hermitian mixed convolution coefficients,
with exponent below the critical threshold, implies the Riemann hypothesis and simplicity of the Xi
divisor.  No analytic hypothesis remains. -/
theorem riemannHypothesis_and_xiZerosSimple_of_mixedSubpower
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hαk : α + 1 ≤ (k : ℝ))
    (hupper : ∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ C * ((N : ℝ) + 1) ^ α) :
    RiemannHypothesis ∧ XiZerosSimple :=
  mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_and_xiZerosSimple
    (mobiusDiscreteLaplaceHalfDecay_of_subpower hk hα hC hαk hupper)

/-- The Riemann hypothesis alone. -/
theorem riemannHypothesis_of_mixedSubpower
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hαk : α + 1 ≤ (k : ℝ))
    (hupper : ∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ C * ((N : ℝ) + 1) ^ α) :
    RiemannHypothesis :=
  (riemannHypothesis_and_xiZerosSimple_of_mixedSubpower hk hα hC hαk hupper).1

/-- **No-go form.**  If the Riemann hypothesis fails then no subpower bound with exponent below the
critical threshold can hold: the Hermitian convolution order exceeds `k - 1`. -/
theorem not_mixedSubpower_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) {k : ℕ} (hk : 0 < k) {α C : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hαk : α + 1 ≤ (k : ℝ)) :
    ¬ (∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ C * ((N : ℝ) + 1) ^ α) :=
  fun hupper => hRH (riemannHypothesis_of_mixedSubpower hk hα hC hαk hupper)

/-- The criterion in the form of an exceeded bound: under a failure of the Riemann hypothesis, every
admissible constant is beaten at some index. -/
theorem exists_lt_mixedAdditiveConvolutionPower_re_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) {k : ℕ} (hk : 0 < k) {α C : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hαk : α + 1 ≤ (k : ℝ)) :
    ∃ N : ℕ, C * ((N : ℝ) + 1) ^ α <
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re := by
  by_contra hcon
  refine not_mixedSubpower_of_not_riemannHypothesis hRH hk hα hC hαk fun N => ?_
  exact not_lt.mp fun h => hcon ⟨N, h⟩

end RHTower
