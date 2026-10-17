# One heat grid, including finitely many offsets, does not determine spectral reality

## Exact failed conjecture

Complete Hankel positivity on a finite collection of offsets of one positive
heat grid forces a conjugation-closed spectrum in `Im(w)^2 < Re(w)` to be real.

Verdict: **FALSE**. This is a statement about the abstract spectral class,
not a counterexample to RH and not a claim that actual Xi has nonreal zeros.

## Obstruction and complete proof

Given grid h>0, offsets tau_i, and any bound B, simultaneous integer
approximation gives n>B with n>0 and
`|n tau_i/h - r_i| <= 1/(2pi)` for integers r_i. Consequently
`cos(2pi n tau_i/h) >= 1/2` for every offset.

Set delta=h/n, b=2pi/delta, a=1+b^2, w=a+ib. Then w is nonreal and lies
strictly inside the stated parabola. Its two-frequency heat trace is
`T(t)=2 exp(-at) cos(bt)`. For every integer m>=0,

`T(tau_i+mh) = [2 exp(-a tau_i) cos(b tau_i)] [exp(-ah)]^m`.

Each bracketed weight is positive. The corresponding polynomial-square
functional equals that positive weight times `p(exp(-ah))^2`, proving all
Hankel ranks nonnegative. Yet `T(delta/2)=-2 exp(-a delta/2)<0`.
The alias frequency can be arbitrarily high because B was arbitrary.

## Strongest positive survivor

Two incommensurate prime-log grids do determine reality of the actual Xi
spectral source through all-degree Hankel positivity. For any K,L>=0, RH is
equivalent to positivity of the sampled literal archimedean-minus-prime source
at times `(2K+1+n)log 2` and `(2L+1+n)log 3`, restricted to their explicit
pole hyperplanes `p(exp(h/4))=0`. The criterion is also equivalent to
vanishing of the literal HJ co-Poisson reflection residual.

Mechanism: absolute summability of heat nodes, principal-ideal trace-Hankel
separation, and injectivity of the pair of prime-log phase clocks. The
principal-ideal generators `X^K(X-exp(h/4))` have no nonreal roots, so neither
finite prefix deletion nor pole cancellation hides a nonreal sample. Two
prime clocks then remove all imaginary aliases.

This is an exact observation theorem. It does not establish the outstanding
all-degree arithmetic sign. All results belong to one cross-route contribution.

## Paper and Lean status

Dependency-closed paper proofs: complete above and in the active twenty-insight card.

Lean modules:

- `RHTower/XiGaussianHeatTwoPrimeSampling.lean`
- `RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean`
- `RHTower/HeatGridAliasingBoundary.lean`
- `RHTower/HeatGridFiniteOffsetAliasing.lean`

All four narrow builds and final individual `lake env lean` audits passed,
without warnings in these modules. All 37 public declarations have only
`propext`, `Classical.choice`, and `Quot.sound` in their axiom closure.
Umbrella imports, index refresh, and `git diff --check` passed. Repository
lint exited 1 on 31 unrelated modules missing umbrella imports in concurrent
OddSector, Bernstein, and HTGeometry work; no error concerns this package.
