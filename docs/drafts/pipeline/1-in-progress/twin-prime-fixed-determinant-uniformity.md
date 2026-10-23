# Fixed determinant, growing affine coefficients

- **ID:** twin-prime-fixed-determinant-uniformity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [undamped cofactor target](twin-prime-nonunit-cofactor-dispersion.md).
- **Statement:** Obtain quantitative Möbius two-point cancellation uniformly for primitive affine forms of fixed determinant four and polynomially growing coefficients.

## Exact candidate

Do there exist absolute `eta,c>0` such that, uniformly for positive
integer slopes `a,c1`, nonnegative intercepts `b,d`, and integer `T`,

`a,c1<=T^eta`, `0<=b<a`, `0<=d<c1`,
`gcd(a,b)=gcd(c1,d)=1`, `|ad-bc1|=4`,

one has

`|sum_(1<=t<=T) mu(a t+b)mu(c1 t+d)| << T/(log T)^c`?

Constants must be independent of all four coefficients. This
is a conjecture, not a Lean premise or a claimed consequence of
the existing fixed-form theorem. A suitable moving initial
endpoint would also need a proved uniform treatment.

## Why this special family appears

On the odd cofactor carrier, `ke-md=2` and `m,k>1` imply
`gcd(m,k)=1`. Choose one solution `d0,e0`; all solutions are
`d=k t+d0`, `e=m t+e0`, with `k e0-m d0=2`.
Restricting to odd physical arguments restricts `t` to one parity.
The resulting two affine forms have determinant four. Their
coefficients can grow, but their determinant does not.

Primitive forms follow from the same equation: every common
divisor of `k,d0` or `m,e0` divides two; odd cofactors remove
that exception. After parity restriction the intercepts are odd.
Reducing intercepts by shifting the parameter must keep the
actual finite interval; it cannot be done independently for
the two forms.

This is more selective than uniformity for arbitrary growing
affine coefficients. The existing source statement excluding
growing coefficients does not itself settle whether its proof
has a useful uniform version on this fixed-determinant family.

## First attack and proof obligation

Audit coefficient dependence in the already-cited primary
ordinary two-point manuscript. Identify each use of:

- primes dividing the determinant;
- heights of the slopes and intercepts;
- lengths and starting points of the parametrizing intervals;
- the passage from Liouville to Möbius and squarefree restrictions.

**[OPEN CORE]** No coefficient-uniform estimate has been proved.
It is not legitimate to turn a fixed-form `o(T)` into this bound
by substituting moving coefficients.

Even a positive logarithmic saving of exponent `c` would not
automatically pay the whole polynomial cofactor range: summing
the absolute logarithmic weights costs up to four logarithms.
The resulting range and every aggregation loss must be calculated
before claiming an application. Mixed and long-cofactor terms
would still remain.

## Gates

- [x] Exact falsifiable uniformity question and arithmetic origin.
- [ ] Internal and primary-source coefficient audit.
- [ ] Verdict after attack; no novelty claim yet.
- [ ] Dependency-closed proof of any surviving estimate.
- [ ] Unconditional Lean certificate without an analytic interface.

## Log

- 2026-10-23 — Isolated fixed determinant four after removing
  damping from the short-cofactor input. The target remains open.
