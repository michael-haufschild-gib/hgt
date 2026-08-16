# SP-E Stokes-wall uniform scale law

- **ID:** SP-E-WALL-UNIFORM-SCALE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** transported Stokes dilation + compact method of moments

## Goal

Identify the canonical arithmetic scale law retained when every fixed prime
coordinate vanishes at the aperture wall. This supplies an actual wall object
for P/SP-E determinant limits and a source-side concentration coordinate shared
with UQ-QC.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and attack identified
- [ ] 1 → 2 fully-proven: dependency-closed paper proof
- [ ] 2 → 3 formalized: closed Lean theorem, target Olean, kernel audit
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

Corpus has the exact wall weight dilation, `W(d) → 4`, generic discrete
half-line laws, exponential compactification, and compact moment weak
convergence. Search found no all-moment or weak-limit theorem for the literal
transported prime scale.

## Conjecturing loop

### C5 — normalized wall scale is uniform

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
finite list of moments.

This is source-derived and target-free. It canonically explains fixed-prime
mass escape and provides the continuum law against which child trace powers
and determinant coefficients must be tested.

## Falsification conditions

C5 fails if normalized weights do not form a probability law, the dilation
identity does not extend to every natural moment, or exponential
compactification does not transport the discrete Laplace values. If bundled
measure construction fails, retain the all-polynomial moment theorem and pivot
through compact moment determinacy later.

## Log

- 2026-08-16 — created after cross-route mass-escape audit; C5 selected.
