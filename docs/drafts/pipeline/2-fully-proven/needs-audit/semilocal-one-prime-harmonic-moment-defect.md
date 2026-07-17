# Semilocal one-prime harmonic moment defect

- **ID:** `semilocal-one-prime-harmonic-moment-defect`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CHANNELWISE TRACE-CLASS NO-GO
- **Scientific status:** `[PAPER-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NEEDS NOVELTY AUDIT] [NOT AN RH PROOF]`
- **Parent:**
  `../../3-formalized/semilocal-all-even-jacobi-prolate-residue-tower.md`;
  `../../1-in-progress/rectangular-semilocal-finite-part-curvature-rh.md`
- **Statement:** The normalized second-moment loss caused by one Euler prime is
  `3*sqrt(2)/(2p)+O(p^-2)`.  Consequently an independent-prime decomposition into a positive
  innovation plus a trace-class correction has nonsummable total trace norm.  This obstruction
  disappears only if the Euler product is assembled before scalar or channelwise splitting.

## Theorem

Let

```text
dmu_infinity(s)=(2*pi)^(-3/2)|Gamma(1/4+i*s/2)|^2 ds,
phi(t)=int exp(i*t*s)dmu_infinity(s)=(cosh t)^(-1/2).
```

This is a probability measure with second moment `1/2`.  For a prime `p`, put

```text
r=p^(-1/2),  ell=log p,
G_p(s)=|1-r*exp(i*ell*s)|^(-2),
dnu_p=G_p dmu_infinity / int G_p dmu_infinity,
m_2(p)=int s^2 dnu_p,
delta_p=1/2-m_2(p).
```

Then

```text
delta_p
 = (3/2) *
   [sum_(m>=1) r^m phi(m*ell) tanh(m*ell)^2]
   /[1+2 sum_(m>=1) r^m phi(m*ell)]                       (1)
 >0,

delta_p=3*sqrt(2)/(2p)+O(p^-2).                           (2)
```

In particular, `sum_p delta_p=infinity`.

Let `H` be a Hilbert space, let `e` be a unit vector, and suppose the one-prime Gram change is
represented by a self-adjoint operator `Delta_p` satisfying

```text
<e,Delta_p e>=-2*delta_p.                                 (3)
```

If

```text
Delta_p=I_p+R_p,
I_p>=0,
R_p self-adjoint and trace class,                         (4)
```

then

```text
||R_p||_1>=2*delta_p.                                     (5)
```

Therefore no independent-prime construction of the form `(4)` can have
`sum_p ||R_p||_1<infinity`.

## Proof of the exact defect formula

The Poisson expansion is absolutely and uniformly convergent:

```text
G_p(s)=(1-r^2)^(-1)
       [1+2 sum_(m>=1) r^m cos(m*ell*s)].                 (6)
```

The common factor `(1-r^2)^(-1)` cancels under normalization.  The archimedean characteristic
function satisfies

```text
int s^2 cos(t*s)dmu_infinity(s)
  =-phi''(t)
  =(1/2)phi(t)-(3/4)phi(t)tanh(t)^2.                      (7)
```

Termwise integration of `(6)` against `1` and `s^2` is justified by the exponential Gamma decay
and the absolutely summable Poisson coefficients.  Thus

```text
int G_p dmu_infinity
 =(1-r^2)^(-1)[1+2 sum_(m>=1)r^m phi(m*ell)],             (8)

int s^2 G_p dmu_infinity
 =(1-r^2)^(-1)
  [(1/2)(1+2 sum_(m>=1)r^m phi(m*ell))
   -(3/2)sum_(m>=1)r^m phi(m*ell)tanh(m*ell)^2].          (9)
```

Dividing `(9)` by `(8)` proves `(1)`.  Every term in its numerator is positive because
`ell>0`; hence `delta_p>0`.

## Proof of the harmonic asymptotic

For every `m>=1`,

```text
r^m phi(m*ell)
 =sqrt(2)*p^(-m)*(1+p^(-2m))^(-1/2).                     (10)
```

The `m=1` term in the numerator of `(1)` is

```text
sqrt(2)/p+O(p^-3),                                       (11)
```

because `tanh(log p)^2=1+O(p^-2)`.  The terms with `m>=2` contribute `O(p^-2)`, while the
denominator of `(1)` is `1+O(p^-1)`.  This proves `(2)`.  Hence there are constants `c>0` and
`p_0` such that `delta_p>=c/p` for every prime `p>=p_0`.  Euler's divergence of
`sum_p 1/p` proves `sum_p delta_p=infinity`.

## Proof of the trace-class obstruction

From `(3)` and `(4)`,

```text
<e,R_p e>=-2*delta_p-<e,I_p e><=-2*delta_p.               (12)
```

Since `e` is a unit vector,

```text
2*delta_p<=|<e,R_p e>|<=||R_p||<=||R_p||_1.              (13)
```

This proves `(5)`, and summing it over the primes gives the no-go.

For the semilocal Gram form, take `e(s)=sqrt(2)s` in the archimedean cyclic space.  Then `e` is a
unit vector and the quadratic form of the normalized one-prime Gram change is exactly
`2m_2(p)-1=-2delta_p`, so `(3)` is the literal first-Jacobi channel.

## Positive survivor: assemble the Euler product first

The theorem excludes an **independent direct sum** of one-prime positive innovations with
summable corrections.  It does not exclude the normalized joint Euler-product measure.  For a
finite nonempty set `P` of distinct primes, write

```text
ell_q=log q,
w(m)=prod_(q in P)q^(-|m_q|/2),
t(m)=sum_(q in P)m_q ell_q.
```

Unique factorization gives `t(m)!=0` for `m!=0`.  The same proof yields the exact joint identity

```text
1/2-int s^2 dnu_P
 =(3/4) *
   [sum_(m in Z^P\{0}) w(m)phi(t(m))tanh(t(m))^2]
   /[sum_(m in Z^P) w(m)phi(t(m))]                        (14)
 >0.
```

Unlike a direct sum of `(1)`, equation `(14)` has one global normalizing denominator and includes
all mixed prime packets before scalarization.  The harmonic lower bound for the sum of isolated
channels therefore does not transfer to the joint product.  This is a mathematically substantive
escape: any viable cofinal Connes--Sonin construction must retain the mixed packets, or an
equivalent non-diagonal prime covariance, until after the compensated relative trace is formed.

## Relation to programme 3

The fixed scalar-Gamma Schur architecture already pays a divergent `sum_p 1/p` capacity cost.
The present theorem shows that replacing it by independent positive one-prime Gram innovations
does not help: their unavoidable negative trace-class corrections have the same harmonic scale.
The only live finite-part route is consequently one of:

1. the normalized full Euler-product Gram operator, with mixed packets kept intact;
2. an explicitly coherent cross-prime covariance whose off-diagonal mass absorbs the local cost;
3. a growing/infinite Gamma-channel carrier; or
4. a principal-relative trace formed before any placewise scalarization.

The RH-bearing theorem is still the all-epsilon cofinal trace-tail estimate for one of these joint
objects.  Nothing in `(1)--(14)` supplies that estimate.

## Corpus and novelty boundary

The corpus already formalizes the exact characteristic function, the strict inequality
`0<m_2(P)<1/2` for every finite nonempty prime set, and the full alternating even-Jacobi residue
tower.  The one-prime source moment problem itself is studied by Connes--Consani--Moscovici,
*On q-series and the moment problem associated to local factors*, arXiv:2403.01247.  The asymptotic
`(2)` and the nonsummable trace-class consequence `(5)` have not yet passed an independent
literature audit, so novelty is provisional.

## Lean boundary

The strict sign input is already formalized as
`semilocalFinitePrimeNormalizedSecondMoment_bounds`.  The abstract implication `(3)--(5)` can be
formalized unconditionally using the existing trace-norm majorization API.  The asymptotic `(2)`
would require a reusable real-series asymptotic layer that is not presently in the project.  No
Lean build should be spent until the joint identity `(14)` and the exact representation of the
cofinal Gram change are selected; otherwise the result would formalize a dead channelwise
architecture rather than the surviving source object.
