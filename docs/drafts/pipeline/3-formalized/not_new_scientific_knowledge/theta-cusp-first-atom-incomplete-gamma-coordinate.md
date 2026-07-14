# Theta-cusp first-atom incomplete-Gamma coordinate

- **ID:** `theta-cusp-first-atom-incomplete-gamma-coordinate`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomGammaIntegral.lean`

## Claim

Let

\[
a_j=2\int_0^\infty x^{2j}\,\thetaCuspSourceTerm(x,1)\,dx.
\]

For every `j : Nat`, Lean proves the unconditional exact value relation

\[
a_j=\frac{2\pi}{4^j}\int_1^\infty (\log t)^{2j}
  \left(2\pi t^{5/4}-3t^{1/4}\right)e^{-\pi t}\,dt. \tag{1}
\]

The proof uses the change of variables `t=exp(2x)`. It also proves continuity on `(0,infinity)`
and absolute integrability on `(1,infinity)` of the transformed integrand. The latter is bounded
by a polynomial times `exp(-t)`, so `(1)` introduces no convergence hypothesis.

## RH leverage

The existing all-order atom domination theorem reduces the first nonconstant prime--Gamma source
Hankel block to two buffered inequalities involving only `a_0,a_1,a_2,a_3`. Equation `(1)` puts
all four values on one fixed domain with one positive elementary density. The remaining proof can
therefore be a finite rational enclosure of four incomplete-Gamma/log moments; it no longer needs
zero locations, a spectral realization, a thermodynamic-limit hypothesis, or control of the
higher theta atoms.

This card does **not** claim either buffered inequality, the first nonconstant source Hankel minor,
or RH. It formalizes the exact coordinate needed for a rigorous analytic certificate of those
inequalities.

## Principal declarations

- `thetaCuspFirstAtomGammaIntegrand`
- `continuousOn_thetaCuspFirstAtomGammaIntegrand`
- `integrableOn_thetaCuspFirstAtomGammaIntegrand`
- `thetaCuspAtomRawEvenMoment_one_eq_gammaIntegral`

## Verification

- [x] exact substitution identity in Lean
- [x] absolute integrability in Lean
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [ ] rational enclosures for `a_0,a_1,a_2,a_3`
- [ ] buffered first-atom inequalities
- [ ] first nonconstant prime--Gamma source Hankel minor

