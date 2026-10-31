# Gamma has a uniform logarithmic dilation modulus

- **ID:** gamma-has-a-uniform-logarithmic-dilation-modulus
- **Stage:** 3-formalized
- **Statement:** There is `C>0` such that, for every `r>0` and real `t`,
  `|gammaHardyPhaseRate(rt)−gammaHardyPhaseRate(t)|≤C|log r|`.

## Proof

Continuity bounds the derivative on `[0,1]`. For `t≥1`, the proved bound
`|γ′(t)|≤1/t²+π/(4t)` gives `t|γ′(t)|≤1+π/4`. Thus one positive constant
bounds `t|γ′(t)|` for every `t>0`. The function `u↦γ(exp u)` has bounded
derivative, hence is Lipschitz by the mean-value theorem. Substitute
`u=log t` and `u+log r`. Evenness covers negative `t`; zero is immediate.

This supplies the uniform Gamma-symbol comparison needed for aperture
transport. It does not yet prove the prime-correlation transport or a new
full Weil floor.

## Verification

`ArithmeticIncidencePositivity/GammaHasALogarithmicDilationModulus.lean`:
`exists_gammaHardyPhaseRate_logarithmic_dilation_bound`.
Programme umbrella wired.

Direct leaf check passed. The capstone axiom audit contains only `propext`,
`Classical.choice`, `Quot.sound`.
