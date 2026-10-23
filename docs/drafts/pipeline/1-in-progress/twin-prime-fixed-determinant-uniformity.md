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
the existing fixed-form theorem. The actual cofactor family has
a canonical parametrization starting at zero, proved below;
arbitrary moving initial intervals are not needed for that family.

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

### Canonical simultaneous intercepts

For odd coprime `m,k>=3`, let `b` be the unique odd integer in
`[1,2k)` with `m b == -2 (mod k)`. The inverse of `m` modulo
`k` exists; its required residue is nonzero since `k` does not
divide two. Its two lifts modulo `2k` have opposite parity, so
exactly one is the required `b`. Put `d=(m b+2)/k`.
This is a positive odd integer, and

`m b+2 <= m(2k-1)+2 < 2mk`,

so `1<=d<2m`. Thus both intercepts are reduced simultaneously,
without separate translations. Also `kd-mb=2`, and every common
divisor of either slope-intercept pair divides two. Odd intercepts
give `gcd(2k,b)=gcd(2m,d)=1`.

Every positive odd solution of `ke-md=2` is then uniquely

`d_var=2k t+b`, `e_var=2m t+d`, `t>=0`.

Indeed the first variable is congruent to `b` modulo `k`; its
oddness strengthens this to congruence modulo `2k`. Subtracting
the two determinant equations supplies the second variable.
The physical interval is exactly

`0<=t<=floor((X-mb)/(2mk))`,

empty when `X<mb`. The corresponding affine determinant is four.
This elementary parametrization does not prove cancellation.

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

## Source-level audit

Inspected the primary
[ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf),
dated 2026-09-24, at §§2--4, 8.4--9 and 18.3. PDF SHA-256:
`ccb6f339a7505db7ab158dae4b739164ed8dda32be4012b0310198dd32f5c70a`.
This is a scoped coefficient audit, not verification of its entire proof.

- Page 7 excludes primes dividing `h*l` and fixes `l` before
  constructing the prime supplies.
- Pages 10--11 encode the modulus coordinate using `ceil(L^15)`
  bits. Its decoding and finite-law estimates absorb `l` into
  the eventual threshold.
- Page 16 splits the rough shift by its class modulo `l` before
  summing centering errors. The calculation below removes that
  particular loss.
- Pages 43--44 set `l=a1*a2`, `h=|a1*b2-a2*b1|`. Their
  progression estimate is normalized by the full interval;
  conversion back to the affine sample absorbs a factor `l`.
- Page 86 obtains Möbius cancellation qualitatively. The
  quantitative theorem there is for Liouville.

Fixed determinant controls `h`, not `l`. To feed the present
question, the required progression error is on the scale `Y/l`,
whereas a uniform `o(Y)` error is insufficient. The canonical
intercepts give `0<c0<l`, so the initial progression prefix has
at most one point; this endpoint causes no growing loss here.

The [coupled-centering calculation](../2-fully-proven/twin-prime-coupled-residue-centering.md)
preserves the congruence inside its Fourier expansion and removes
the residue-class summation loss. A square-divisor truncation
also proves its Möbius version, against any unit-bounded second
row. This does not supply the missing factor `1/l` or a
quantitative fixed-affine Möbius theorem. Replacing the single
modulus coordinate by a better encoding alone also cannot repair
that normalization.

**[OPEN CORE]** Prove cancellation relative to the actual number
of affine samples, uniformly in the stated coefficients, and with
the actual Möbius factors. No such estimate has been proved here.
Verdict: **SURVIVES PRELIMINARY ATTACK**, unproved; no novelty
claim. The inference from fixed-form cancellation is rejected,
not the uniform conjecture itself.

Even a positive logarithmic saving of exponent `c` would not
automatically pay the whole polynomial cofactor range: summing
the absolute logarithmic weights costs up to four logarithms.
For `m,k<=X^beta`, the shortest parameter length is of order
`X^(1-2beta)`. A slope range `T^eta` covers these faces only when
`beta<eta/(1+2eta)`. One absolute `eta` would therefore not cover
every cutoff below the square-root threshold.

The absolute aggregation cost is
`(sum_(m<=Z) log(m)/m)^2=O(log^4 Z)`; the starting-point terms
cost `O(Z^2 log^2 Z/X)`. Thus a power cutoff requires a saving
exponent greater than four under this termwise argument. Any
positive exponent `c` would instead pay
`Z=exp((log X)^alpha)` for `0<alpha<min(1,c/4)`, provided the
coefficient-uniform estimate itself were established. These are
deductions about the proposed estimate, not proved cancellation
bounds. Mixed and long-cofactor terms would still remain.

## Gates

- [x] Exact falsifiable uniformity question and arithmetic origin.
- [x] Internal and primary-source coefficient audit at the stated scope.
- [x] Verdict after attack; no novelty claim.
- [ ] Dependency-closed proof of any surviving estimate.
- [ ] Unconditional Lean certificate without an analytic interface.

## Log

- 2026-10-23 — Isolated fixed determinant four after removing
  damping from the short-cofactor input. The target remains open.
- 2026-10-23 — Audited the source's modulus, normalization and
  Möbius dependence; proved the canonical zero-start geometry
  and derived the exact attainable cofactor range. The coupled
  Fourier calculation removes one proof loss but not the core.
