# SP-E Stokes-wall uniform scale law

- **ID:** SP-E-WALL-UNIFORM-SCALE
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** transported Stokes dilation + compact method of moments

## Goal

Identify the canonical arithmetic scale law retained when every fixed prime
coordinate vanishes at the aperture wall. This supplies an actual wall object
for P/SP-E determinant limits and a source-side concentration coordinate shared
with UQ-QC.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and attack identified
- [x] 1 → 2 fully-proven: dependency-closed proof
- [x] 2 → 3 formalized: closed Lean theorem and stronger wall-kernel consequences
- [ ] 3 → 4 publication-ready: standalone theorem/proof/certificate

## Corpus audit

Queries run before conjecturing:

- `Stokes wall transported prime weight uniform measure moments p power dilation`
- `aperture child kernel continuum integral operator cubic Cauchy wall`
- `Eulerian limit cubic coherence uniform measure determinant`
- `routePPrimitiveGammaJuliaStokes wall moment all polynomial test functions`
- `compact moment weak convergence probability measures Hausdorff polynomial moments`
- `countable atomic probability measure weights tsum one dirac`
- `uniform probability measure Icc zero one moments one over k plus one`

Corpus now has exact wall weight dilation, `W(d) → 4`, all power moments,
weak convergence of compactified wall law to uniform measure on `[0,1]`, and
equivalent convergence of logarithmic coordinate to unit exponential law.

## Formal theorem

### Normalized wall scale is uniform

For `d>0`, let

```text
w_d(p) = 8 d log(p) p^(-1-2d),
W(d) = sum_p w_d(p),
A_d(p) = 2d log(p),
X_d(p) = exp(-A_d(p)) = p^(-2d).
```

Normalize prime `p` by probability weight `w_d(p)/W(d)`. Exact dilation gives,
for every natural `k`,

```text
E[X_d^k] = W((k+1)d) / ((k+1)W(d)) → 1/(k+1).
```

These are exactly moments of uniform probability on `[0,1]`, equivalently
Laplace values of Exp(1) for `A_d`. Compact Hausdorff determinacy therefore
forces weak convergence of the full normalized prime-scale law, not merely a
finite list of moments. Lean proves this through
`tendsto_wallCompactLaw_nhdsGT_zero`, `tendsto_wallHalfLineCDF_nhdsGT_zero`, and
`tendsto_integral_wallCubicCoherence_prod_nhdsGT_zero` in
`RoutePPrimitiveGammaJuliaStokesWallCubicCoherenceWeakLimit.lean`.

This theorem is source-derived and target-free. It canonically explains fixed-prime
mass escape and provides the continuum law against which child trace powers
and determinant coefficients must be tested.

## Stronger formal consequences

- Exponential cubic-coherence expectation is exactly `16/35`.
- Child Hilbert--Schmidt energy converges to `256/35` and has a positive finite-wall floor.
- Quantile-pulled cubic kernel converges in `L2` on one fixed carrier.
- Balanced determinant square jet is eventually bounded away from zero.
- Every fixed factorial-normalized continuum Fredholm coefficient has a wall limit by complete
  signed-permutation expansion and Hadamard domination.

These close wall law, quadratic noncollapse, and fixed-order continuum coefficients. Open SP-E/P
gate is identification with finite physical child coefficients plus one summable order-majorant
giving locally uniform entire convergence, followed by completed-Xi divisor identification.
