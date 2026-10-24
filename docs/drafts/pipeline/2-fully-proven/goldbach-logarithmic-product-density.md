# The product density as a compensated logarithmic entry convolution

- **ID:** goldbach-logarithmic-product-density
- **Stage:** 2-fully-proven
- **Type:** Classical continuous arithmetic bridge; no novelty claim
- **Parent:** [flat prime-dilation dispersion](goldbach-flat-prime-dilation-dispersion.md)
- **Source:** `RHTower/LogarithmicLinearEntryConvolution.lean`
- **Lean status:** Full logarithmic identity, indicator reading, triangular form, bounds, and strict support written in `goldbach/BalancedProductLogDensity.lean`; direct leaf verification and six closure audits pending.

## Exact statement

For every positive integer X put a=log X, b=log(2X), and

    W_X(s)=1_(a≤s)−1_(b≤s),
    R_X(t)=(t−2a)₊−2(t−a−b)₊+(t−2b)₊.

The entries are the actual `RHTower.logarithmicUnitEntry` functions.
For every real t, including negative t,

    ∫_(0..t) W_X(s) W_X(t−s) ds = R_X(t).       (C)

The integrand is interval-integrable on every finite real interval.
The window equals the indicator of [a,b), and

    R_X(t)=max(min(t−2a,2b−t),0),
    0≤R_X(t)≤log 2,
    R_X(t)>0 ↔ 2a<t<2b.                         (T)

Thus the compensated four-ramp expression is a nonnegative triangular
profile with fixed height log 2. It is the logarithmic expression
for the piecewise product density used in the parent paper.

## Dependency-closed proof [PROVED HERE]

The source theorem gives, for each pair u,v≥0,

    ∫_(0..t) 1_(u≤s) 1_(v≤t−s) ds=(t−u−v)₊,

and proves the corresponding interval integrability. Here a,b≥0
because X is a positive integer. Expanding both window differences
produces four integrable terms. Their integrals have endpoints
(a,a), (a,b), (b,a), (b,b), so their signed sum is precisely (C).
No interchange of infinite sums or limiting argument occurs.

Since b−a=log 2>0, subtracting the two step functions gives the
indicator of [a,b). For (T), split the real line at 2a,a+b,2b.
The signed ramp sum is respectively 0, t−2a, 2b−t, and 0.
These four formulas equal the displayed clipped minimum, whose
nonnegativity and strict support are immediate. The two affine
pieces meet at height b−a=log 2, proving the uniform upper bound.

## Corpus and attack audit

The existing RH entry-convolution theorem is a direct source for
this statement. Its finite-difference specialization is classical,
not a scientific novelty. The four signed terms are all retained;
positivity follows from their exact compensation. The change of
variables identifying this logarithmic convolution with the product
Lebesgue measure and the curved-lattice discrepancy remain separate
obligations. No analytic cancellation or Goldbach proof is asserted.

## Log

- 2026-10-24 — Located the exact RH unit-entry convolution and derived
  its full finite-window specialization, triangular form, bounds,
  and strict support. Started formalization of these exact statements.
