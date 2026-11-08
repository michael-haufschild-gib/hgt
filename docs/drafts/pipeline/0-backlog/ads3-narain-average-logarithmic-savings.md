# Rapid logarithmic savings at the Narain boundary

- **ID:** W11-NL
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Unconditional boundary rate](../1-in-progress/ads3-narain-average-boundary-rate.md)

## Conjecture

For every positive target-height pair `Y,Z` and every integer `N≥0`,

`yA_YZ(y)+(3/π)log y−B_YZ = o(y^(1/2)|log y|^(−N))` as `y→0+`.

A sufficient stronger statement is that the actual boundary value
`t↦narainMellinMean Y Z (it)` is a Schwartz function.
The exact boundary contour identity would then turn the remainder divided
by `y^(1/2)` into a Schwartz Fourier transform evaluated at `log y`.

## Mechanism to audit

`RHTower.BAGTrace.exists_residue_global_polynomial_disks` gives zero-free
disks of radius `c(1+|t|)^(−9)` around `σ+it`, `1≤σ≤2`, together with
polynomial bounds for the pole-removed zeta factor and its reciprocal.
`exists_residue_derivative_polynomial_bounds` already supplies every
reciprocal derivative. Both are in `ChiRamanujanGlobalResidueControl.lean`;
their transitive kernel audits remain required.

A direct Cauchy argument avoids expanding quotient derivatives. Pull the
disks back by `z=1+2u`. The actual Narain strip estimate retains exponential
decay there, because reciprocal zeta costs only a polynomial and the
imaginary height changes by a bounded amount. Cauchy's estimate for the
`n`th derivative adds the factor `r^(−n)`, hence another polynomial of
degree `9n`. Central removability controls the compact part of the line.
Thus every derivative should retain exponential decay, implying Schwartz
membership of the actual boundary value.

`RHTower.xiCSchwartz` concerns the centered xi restriction itself, not this
quotient. The pulled-back disk bounds, real-line derivative transport,
Schwartz construction and Fourier identification remain to be formalized.

This conjecture improves the boundary by logarithmic factors only. It
supplies no exponent above `1/2` and no RH-strength estimate.

## Gates

- [ ] 0 → 1: audit all-order derivative bounds and Fourier transport.
- [ ] 1 → 2: prove Schwartz membership for the actual boundary value.
- [ ] 2 → 3: direct Lean checks, transitive axiom audits and umbrella imports.
