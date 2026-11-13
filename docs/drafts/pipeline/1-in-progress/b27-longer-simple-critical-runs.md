# Longer consecutive simple critical runs

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-1311/route-obstacles.md`, B27.
- **Target:** Arbitrarily long consecutive occupied ordinates of the actual ξ divisor, each of total multiplicity one. First unresolved length: six.
- **Status:** Open; no new unconditional run theorem.

## Exact existing input

`IncommensurableGaborPinching/ConsecutiveSimpleCriticalZeros.lean` proves
`xi_five_runs_one_five_thousandth`. With `N` zero copies, `S` simple critical zeros,
`C` singleton ordinates and `O` occupied ordinates, its finite inputs are

\[
2O+S\le N+2C,\qquad
R_{k+1}\ge(k+1)C-kO-k.
\]

The analytic inputs give lower densities `S/N ≥ H` and `C/N ≥ H−11π/2000`,
where `H=HD(1)`. At length six their combination gives
`R₆ ≥ C+(5/2)S−(5/2)N−5`, with negative certified coefficient.
The stronger local lens census in `RHTower/LensIsolatedSimpleZeros.lean`
protects only a vertical radius `π/(2L)` on the critical line; mean copy spacing is `2π/L`.

## What needs new information

Scalar censuses do not determine long runs. The repeated multiplicity word
`(1,1,1,1,1,2)` has `S=C=5N/7` and no six singleton ordinates.
Even the boxcar Gram does not remove this example: put the repeated period-seven
word `(1,1,1,1,1,2,0)` on the integer lattice. All nonzero differences are integers,
so the sinc correlations vanish; normalized squared Gram energy is `9/7 < 4/3`.
This is an obstruction to those input inequalities, not a model of ζ.

The missing input must constrain the ordering of the actual divisor beyond these
censuses and a single boxcar window. A possible source is simultaneous signed
prime-side control of several profiles, retaining correlations between simple and
multiple/off-line fibres. Existing disjoint-pair pinching extracts only pairs of
simple critical zeros; it does not yet supply this constraint.

## Gates

- [x] Exact target and existing theorem located.
- [ ] Dependency-closed proof of six consecutive singleton ordinates.
- [ ] Extension to every finite length.
- [ ] Lean formalization and transitive axiom audit.
