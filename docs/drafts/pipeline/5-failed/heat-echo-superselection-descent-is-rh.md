# Heat-echo-to-superselection descent is exactly RH

- **ID:** `heat-echo-superselection-descent-is-rh`
- **Stage:** 5-failed
- **Type:** THEOREM / TERMINAL ROUTE VERDICT
- **Scientific status:** `[PROVED; BRIDGE; RH ROUTE CLOSED]`
- **Source:** `additive-heat-aperture-zeta-zero-echo.md` and
  `prime-poisson-superselection-screen.md`
- **Statement:** The proposed implication from disappearance of the additive heat echo to existence
  of a reflected prime-sector morphism is equivalent to RH.  The canonical nonzero on-zero tangent
  fails sector covariance at every hypothetical off-line zero, so the heat construction does not
  supply the missing implication.

## The two independently proved predicates

Work in the right Goldilocks strip

```text
S_+ = {s : C : 1/2 < Re(s) < 1}.
```

Let `EchoDefect(s)` mean that the coefficient of

```text
x^((s-1)/2)
```

in the additive heat-aperture expansion vanishes.  The heat-aperture theorem proves

```text
EchoDefect(s) iff zeta(s)=0.                            (1)
```

Let `SectorCompatible(s)` mean any of the equivalent reflected-sector conditions already proved:

```text
mu_s is measure-class equivalent to mu_(1-conj(s)),

sum_p |p^(-s)-p^(-(1-conj(s)))|^2 < infinity,

the two reflected coherent prime representations are normally equivalent.
```

The prime Poisson/Kakutani theorem and the prime-clock Shale theorem prove

```text
SectorCompatible(s) iff Re(s)=1/2.                     (2)
```

The left side of (2) is false throughout `S_+`.

## Exact equivalence

`[PROVED]` The claimed descent

```text
for every s in S_+,
EchoDefect(s) implies SectorCompatible(s)               (3)
```

is equivalent to zero-freeness of zeta on `S_+`.

By (1)--(2), (3) is exactly

```text
for every s in S_+, zeta(s)=0 implies Re(s)=1/2.
```

Since `Re(s)>1/2` on `S_+`, this says that `S_+` contains no zeta zero.  Functional-equation and
Schwarz reflection then exclude the left half of the critical strip as well.  Conversely RH makes
`S_+` zero-free, so (3) holds vacuously.  Hence (3) is RH.

This is not merely the observation that the final theorem would imply RH.  The two predicates that
the route independently constructs are already exactly the zero predicate and exactly the critical
line predicate.  No third relation between them has been derived.

## The canonical tangent does not supply the relation

Let

```text
f_s(theta)=sum_(n>=1) n^(-s) exp(in theta)
```

in its `L2` range, and subtract its universal singular branch:

```text
R_s(theta)
  = f_s(theta)-Gamma(1-s)(-i theta)^(s-1).
```

The local polylogarithm expansion gives

```text
R_s(theta)
  = zeta(s)+i zeta(s-1)theta+O(theta^2).                (4)
```

At a zero `rho in S_+`, the tangent

```text
T(rho)=zeta(rho-1)                                     (5)
```

is nonzero.  Indeed `-1/2<Re(rho-1)<0`; the zeta functional equation sends this strip to
`Re(2-rho)>1`, where the Euler product is nonzero, and no trivial zero occurs there.

This closes the nonvanishing requirement that defeated scalar value-level witnesses.  It does not
close covariance.

For a prime `p`, the two reflected one-prime characters are

```text
alpha_s(p)=p^(-s),
alpha_tau(s)(p)=p^(-(1-conj(s))).
```

The covariance defect of the scalar tangent is

```text
D_p(s)
  = T(s) alpha_s(p)-alpha_tau(s)(p)T(s)
  = zeta(s-1)(p^(-s)-p^(-(1-conj(s)))).                (6)
```

At `rho in S_+` with `zeta(rho)=0`, equation (5) makes the first factor in (6) nonzero.  Therefore

```text
D_p(rho)=0
  iff
p^(-rho)=p^(-(1-conj(rho)))
  iff
Re(rho)=1/2.                                           (7)
```

The last equivalence follows by taking absolute values.  It holds for one prime, hence also for the
full prime algebra.

Thus the canonical source tangent is nonzero at every zero but is an on-shell sector intertwiner
only if RH already holds.  Its covariance defect does not factor through `zeta(s)` without assuming
the desired zero localization: at a hypothetical off-line zero the denominator in
`D_p(s)/zeta(s)` vanishes while the numerator does not.

The same argument applies to any scalar or one-dimensional defect value that is nonzero at the
zero.  Intertwining two one-dimensional prime characters forces equality of those characters, which
is precisely the critical-line selector.

## Why the heat measurement does not contradict an off-line zero

Assume hypothetically that `rho in S_+` is a zeta zero.  Every proved object remains consistent:

- `Psi_rho` is an ordinary normalizable rank-one vector;
- its prime Poisson measure is equivalent to Haar;
- its reflected measure is singular and disjoint;
- the finite-aperture heat energy is strictly positive for every aperture;
- the subleading echo is absent by (1); and
- the additive tangent (5) is nonzero but noncovariant by (7).

There is no contradiction.  The heat echo is an additive boundary coefficient of a bulk vector;
its disappearance does not change the representation class of that vector.  Superselection says
what a normal reflected morphism would force, but the zero does not manufacture such a morphism.

## Continuous and meromorphic repairs remain closed

The already formalized continuous-witness theorem proves that a continuous family of normal
reflected-sector intertwiners supported on the critical line vanishes identically.  A meromorphic
family that intertwines on every regular fiber also vanishes by analytic continuation.  Therefore a
repair would have to assert a singular on-shell covariance factorization

```text
T(s)alpha_s(p)-alpha_tau(s)(p)T(s)=zeta(s)R_p(s),       (8)
```

with `T(rho)!=0` at every zero.  But evaluating (8) at a zero gives exactly (3).  Constructing (8)
from the source is therefore the full RH theorem, not a remaining technical lemma.

## Terminal verdict

`[CLOSED AS AN RH ROUTE]` The superselection idea correctly constructs the critical wall.  The heat
aperture correctly constructs a positive full-density zero detector.  Their conjunction does not
prove that the detector's defects inhabit the wall.

The route dies at the attempted category change

```text
additive scalar/asymptotic defect
  ->
normal multiplicative-sector morphism.
```

No functor, positivity theorem, covariance identity, or source law performs this change.  Requiring
one is equivalent to RH by (1)--(3), and the canonical nonzero tangent fails it by (6)--(7).

The heat-aperture theorem survives independently as a source measurement theorem.  What is retired
is the claim that superselection turns that measurement into a proof of RH.

## Gates

- [x] heat defect identified exactly with the zeta divisor
- [x] sector compatibility identified exactly with the critical line
- [x] desired descent proved equivalent to RH
- [x] canonical nonzero tangent constructed and its covariance defect computed
- [x] hypothetical off-line zero checked against every proved object with no contradiction
- [x] route moved to 5-failed; no Lean wrapper added for the tautological final equivalence
