# Dyadic sharp positive-excess energy spectrum

- **ID:** `dyadic-sharp-positive-excess-energy-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM / quantitative RH gate
- **Scientific status:** `[FORMALIZED] [LITERATURE BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `dyadic-sharp-positive-excess-energy-rh-gate.md`

## Theorem

Put
\[
 W(n)=\sum_{n/2<k\le n}\frac{\Lambda(k)}{\sqrt{k}},\qquad
 E(n)=\left(W(n)-2(1-2^{-1/2})\sqrt n\right)_+.
\]
For every `alpha >= 0`, convergence at the single real abscissa
\[
 \sum_{n\ge1}\frac{E(n)}{n^{1+\alpha}}<\infty
\]
forces every nontrivial zeta zero to satisfy
\[
 \Re\rho\le \frac12+\alpha.
\]

This is strictly more informative than the banked all-epsilon implication to RH: it turns the
abscissa of positive-excess energy into a quantitative horizontal zero-free bound.  The proof
factors the existing two-stage Landau transfer so that it consumes one correction-series
abscissa below a hypothetical transverse boundary.

## Formal artifact

`formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowEnergySpectrum.lean`

Principal declaration:

`xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable`

## Gates

- [x] exact source-negative-part / prime-window-positive-excess identity already formalized
- [x] numerical consistency check for the Landau radii
- [x] factor the one-abscissa Landau transfer
- [x] prove the fixed-alpha zero-free law in Lean
- [x] prove the direct positive-excess theorem surface
- [x] exact module build and axiom audit
- [x] conservative novelty audit: Landau/weighted-Chebyshev bridge, not advertised as an
  independent new method
- [x] retained as source-side quantitative context; not used as the rectangular paper headline

## RH boundary

The theorem is conditional on the displayed arithmetic energy.  Proving that energy for every
positive `alpha`, or at `alpha = 0`, remains RH-bearing.
