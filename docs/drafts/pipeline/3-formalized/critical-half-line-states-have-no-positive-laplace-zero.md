# Critical half-line states have no positive Laplace zero

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B104; a spectral constraint without positivity of the state.
- **Statement:** At the finite global window threshold, every actual critical state F satisfies `L_F(s)=∫ F(u) exp(su) du ≠ 0` for every real `s>0`.
- **Status:** Verified in Lean; umbrella wired.

## Exact reflection argument

Assume `L_F(s)=0`. Put
`G(u)=∫_{v<u} exp(-s(u-v)) F(v) dv` and `H=-F+2sG`.

1. The vanishing total Laplace coefficient makes G and H vanish on `[0,∞)`.
   Both have the required actual weighted integrability; H has full Gamma
   integrability.
2. The reflection multiplier has modulus one. It preserves full Gamma
   energy and, by polarized Plancherel, every translated correlation and
   the complete prime sum.
3. The causal and anti-causal representations give
   `L_F(q)=(s-q)L_G(q)` and `L_H(q)=(s+q)L_G(q)`.
   Thus the opposite pole-moment product is invariant, including `s=1/2`.
4. Exponential weighting shifts the resolvent rate. The exact L² identity is
   `I₈(F)-I₈(H)=16s I₈(G)`, hence
   `Q(H)=Q(F)-16s α(W₀)I₈(G)`.
5. Endpoint nonnegativity and zero critical energy force `I₈(G)=0`.
   Injectivity of the actual causal resolvent forces F to vanish almost
   everywhere, contradicting its unit norm.

No classical derivative, smoothness, positivity, polar-threshold equality,
or unproved factorization input is used. Every domain field is discharged.

## Lean

Module: `ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateHasNoPositiveLaplaceZero`.

- `criticalHalfLineFullEnergy_realCausalReflection`: exact full-form defect.
- `ae_eq_zero_of_criticalHalfLineFullEnergy_eq_zero_of_laplace_zero`: every actual-domain zero-energy profile with one positive Laplace zero vanishes almost everywhere.
- `criticalHalfLineGroundState_laplace_ne_zero`: actual-state nonvanishing.
- `riemannHypothesis_or_exists_laplaceZeroFree_criticalHalfLineGroundState`: unconditional dichotomy.

Verified support modules:
`CausalExponentialZeroReflection`, `CausalExponentialReflectionEnergy`,
`WeightedCausalExponentialReflection`, `RealCausalExponentialReflection`,
`FourierModulusDeterminesActualCorrelation`, `CausalExponentialLaplaceReflection`,
`TheCausalReflectionPreservesPrimeAndGammaEnergy`, and
`TheCausalReflectionPreservesThePoleProduct`.

The [actual-domain and weak-equation framework](critical-half-line-states-have-causal-logarithmic-coordinates.md)
supplies endpoint nonnegativity and zero energy. The arithmetic polar source
is not identified with a positive Laplace moment; its nonvanishing remains open.
