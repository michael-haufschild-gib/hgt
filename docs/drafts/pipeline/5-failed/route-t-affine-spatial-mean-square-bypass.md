# Route T affine spatial mean-square bypass

## Status

- Route: T
- State: failed/retired
- Date: 2026-08-11
- [x] corpus-wide relevant-module audit
- [x] exponent obstruction isolated
- [x] strongest positive survivor formalized in Lean
- [ ] final umbrella build/lint/axiom audit

## Retired target

Derive a prime-gap square moment with exponent below `3/2` directly from the corpus's affine
Dirichlet-polynomial mean squares, Gallagher short-window bounds, global prime number theorem, and
Selberg/Brun prime-window upper bounds, bypassing Maynard's large-value decomposition.

## Exact obstruction

The affine/Gallagher estimates control an uncentred square for arbitrary coefficient sequences.
For von Mangoldt or prime-log coefficients, their diagonal mass is legitimate but they do not
produce the matching second-moment main term needed to cancel the square of the expected interval
mass. Global PNT supplies the first moment only. Combining it with a Selberg/Brun upper bound leaves
a constant-times `X H^2` contribution to the centred spatial mean square. That scale gives no
power-saving empty-interval estimate and cannot force a gap-square exponent below `3/2`.

The corpus's pointwise PNT error `X exp(-c sqrt(log X))` also cannot replace this cancellation: it is
larger than `X^(1-delta)` for every fixed `delta>0` eventually. Existing interval-sieve modules are
upper-bound sieves and do not supply a lower-bound or asymptotic prime-pair main term. Thus this
specific assembly has no path to the Route-T threshold; adding more uncentred affine estimates is
rate theatre.

## Strongest positive survivor

Route T needs a gap-square exponent `1+nu` for any `nu<1/2`, not Maynard's optimal `nu=1/4`.
`Sieve/MaynardWeakLargeValues.lean` formalizes the resulting weaker large-value geometry. If two
complementary factors satisfy their height-dominated Montgomery bounds, then

```text
R <= T M^(1-2 alpha),
R <= T N^(1-2 beta),
x = M N,
x^sigma = M^alpha N^beta
```

imply exactly

```text
R <= T x^(1/2-sigma).
```

Therefore the Route-T target `R <= T x^(1+nu-2sigma)` holds throughout
`sigma <= 1/2+nu`. At `nu=49/100`, Lean closes every level `sigma<=99/100` without `R*`.
The same file proves exact unbalanced and sixth/second-moment interpolation laws, reducing the
remaining high-`sigma` band to explicit product-length inequalities.

## New insight

The apparent `R*` wall is partly an artefact of optimizing the historical `5/4` exponent. For
Route T, complementary second moments already close all but a thin near-maximal-value band. The
live arithmetic problem is now pointwise/large-value exclusion in that band plus factor grouping,
not a wholesale formalization of Heath--Brown additive-energy machinery.

## Log

- 2026-08-11 — spatial affine/PNT/sieve bypass audited and retired; weak-exponent Montgomery
  interpolation survivor formalized and direct-checked.
