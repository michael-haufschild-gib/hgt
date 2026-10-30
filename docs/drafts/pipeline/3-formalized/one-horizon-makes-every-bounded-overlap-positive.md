# One horizon makes every bounded overlap positive

- **ID:** one-horizon-makes-every-bounded-overlap-positive
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

For the explicit tilted unit spline and every `K>0`, there are `e_K>0` and
`N_K` such that, simultaneously for all `N≥N_K` and `0<c≤K`, every eigenvalue
of the actual complete Weil matrix at width `c/N` is at least `e_K`.
Consequently every signed atomic coefficient packet has nonnegative
complete Weil form at that common horizon.

This exchanges the fixed-overlap theorem's horizon and overlap quantifiers.
It permits arbitrary moving overlap sequences bounded by `K`.

## Proof [PROVED HERE]

Replace `K` by `L=max(1,K)`. Uniform weighted affine shell readings and
their harmonic norm bound supply the signed reciprocal source. A common
finite offset range gives uniform logarithmic and horizon-cutoff errors.
Thus the literal upward prime residual vanishes uniformly for `1≤c≤L`.
The exact near-Gamma/downward cancellation, near center bound, and remaining
replacement estimates give uniform complete conductor norm quasimodes.

A positive Fourier minimum on `[1,101L]`, one ordered cutoff, and the
uniform signed arithmetic source yield a common complete defect reserve
`W_N(c)≥a D_N−C S_N`, with `a>0`. Every bounded-energy unit vector therefore
has at least `1/18` coordinate mass in one fixed finite Ramanujan family,
independent of `c`.

The positive coprime-tail formula bounds every completed conductor energy
below by `e=2/M ∫_{t>L}|φ̂(2πt)|²dt>0`. If a unit eigenvector had eigenvalue
below `e/2`, its coordinate against each of the finitely many conductor
quasimodes would be bounded by its uniform residual divided by the gap
`e/2`. At a common horizon their total squared coordinate mass is less
than `1/18`, a contradiction.

For `0<c≤1`, the existing uniform through-touching theorem applies to the
same threshold: conductor one's endpoint energy equals the completed shape
and is at least `e`. Intersect the two horizons. The Hermitian spectral
identity gives the full coefficient-vector bound and the literal atomic
Weil inequality.

## Lean status

`CriticalArithmeticCorrelationTheory/OneHorizonMakesEveryBoundedOverlapPositive.lean`
proves the common spectral floor, positive definiteness, coefficient energy
floor and literal signed atomic Weil nonnegativity. All supporting source,
cancellation, replacement, reserve and quasimode leaves passed final direct
Lean checks. The four capstone axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`; umbrella imports are wired.

Counted as contribution 10, including all supporting uniform estimates.

Corpus comparison finds uniform positivity through `c=1`, and positivity
for each fixed arbitrary `c`; neither gives one horizon for every `c≤K`.
The contribution is the actual common positivity horizon, including all
supporting source estimates, rather than separate counts for its lemmas.

## Boundary

No prescribed unbounded overlap schedule or RH conclusion follows from
this bounded-overlap theorem.
