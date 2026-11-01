# Finite-field approximation of ξ: route audit

- **ID:** finite-field-approximation-route-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, §2.4.
- **Scope:** distinguish the literal Euler-product proposal from approximation by centered curve numerators; no claim to prove RH.

## Exact obstruction

For a curve, the change `u = a s + b`, `a > 0`, centers its zeros at `Re s = 1/2` precisely when `b = (1-a)/2`. Its Euler product converges only for `Re s > (1+a)/(2a)`. Thus effective mesh `a log q → 0`, with `q ≥ 2`, moves the convergence half-plane to infinity. Analytic continuation of the numerator remains possible; ordinary Euler-product convergence on `Re s > 1` does not.

## Positive survivor under audit

Paired, centered curve numerators are positive multiples of products `cosh(h z) - cos θ`, with `h = a log q` and `z = s-1/2`. Their nonnegative even coefficients suggest the exact radial bound `|F(z)| ≤ F(R)` for `|z| ≤ R`. Consequently real-axis convergence on an unbounded set would itself supply local boundedness. This is an analytic reduction, not an arithmetic producer.

## Corpus

- `RHTower/XiCRealZeroVitaliBlowup.lean`: Vitali–Hurwitz receiver and local blow-up alternative.
- `ArithmeticResonanceTheory/OverFiniteFieldsTheOddPartIsSpectral.lean`: spectral zeros, vertical periods, unitarity calibration; not a formalization of Weil–Deligne.
- `ArithmeticResonanceTheory/TheArchimedeanPlaceForbidsFiniteVirtualRealizations.lean`: excludes exact finite realizations, not limits.

## Open core

Construct specified curves and specified scalar/exponential normalizations from arithmetic, and prove their centered numerators converge to `ξ(1/2+z)` on the positive real axis. No such construction was supplied by §2.4. Generic geometric realizability or selection using ζ's zero locations does not discharge this obligation.
