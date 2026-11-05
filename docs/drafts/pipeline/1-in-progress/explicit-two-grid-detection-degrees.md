# Explicit degrees for two heat grids

- **ID:** explicit-two-grid-detection-degrees
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0511, A18.

## Target

Quantify the polynomial degree detecting each off-line ξ-zero on one of the
prime-log grids `log 2`, `log 3`, including arbitrary starting offsets and the
arithmetic source's pole constraint.

## Candidate bound

Write `λᵢ=exp(−h zᵢ²)` and choose a nonreal target `α=λᵢ₀`, `r=|α|`.
The existing reciprocal-square mass and heat-term bounds give
`Σ|λᵢ|≤M=6/h`. Let `F` contain the distinct sampled nodes with modulus at
least `r/2`. Then `#F≤ceil(2M/r)`.

For the ideal generator `a`, use `c=sqrt(−1/α)` and the existing real orbit
separator with target value `c/a(α)`. Let `E` be its explicit coefficient norm
bound on the radius-`r` disc, multiplied by the coefficient norm bound of `a`.
Set `n=ceil(log(1+2E²M)/log 4)+1`.

The phase-corrected radial factor gives tail norm at most `E²M·4⁻ⁿ<1/2`.
Every retained copy of the target or its conjugate contributes `−1`; all
other outer nodes vanish. Thus the trace-Hankel value is below `−1/2`, with
separator degree at most `2#F+1+n`.

For the source grid take `a=X^K(X−exp(h/4))`; the test degree is at most
`2ceil(2M/r)+2+n`. The finite spectral set and its separation products remain
in `E`; this is not yet a bound in height and depth alone.

## Dependencies and gap

`TraceHankelConverse.lean` supplies the exact separator, target values,
coefficient norm bound and qualitative inner-tail decay. The missing steps
are the uniform geometric tail, degree bookkeeping, explicit total heat mass,
and their transport to the actual two-grid arithmetic source.
