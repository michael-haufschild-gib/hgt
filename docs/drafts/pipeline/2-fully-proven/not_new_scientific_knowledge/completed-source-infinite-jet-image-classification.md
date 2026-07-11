# Exact completed Euler-source image in infinite flux-jet space

- **ID:** `completed-source-infinite-jet-image-classification`
- **Stage:** 2-fully-proven / not-new
- **Type:** theorem (paper), `[BRIDGE]`
- **Statement:** After subtracting the fixed archimedean channel, a residue-filled infinite
  completed-flux jet belongs to the degree-one Euler-source image exactly when its uniquely
  continued far-right germ is an absolutely convergent Dirichlet series whose canonically extracted
  coefficients are supported on prime powers and satisfy every quadratic Euler ray equation.  The
  parameter field is then unique.  The zeta source is the sublocus on which every recovered prime
  parameter equals `1`.

## Jet and continuation data

Fix a point `rho` in the open critical strip.  A residue-filled completed-flux jet is a sequence

```text
j=(j_0,j_1,...)
```

whose power series

```text
g_j(x)=sum_(k>=0) j_k x^k
```

converges near `x=0`.  On the punctured germ define the corresponding raw completed flux by

```text
F_j(rho+x)=g_j(x)/x.                                  (1)
```

At a zero, `j_0` is the negative multiplicity; at a regular point it is zero.  Suppose (1) has a
single-valued meromorphic continuation to a connected domain meeting the Euler half-plane

```text
H_1={s : Re s>1}.
```

The continuation, when it exists, is unique by the identity theorem.  Let

```text
B_arch(s)=-logDeriv(archFactor)(s)
```

be the fixed archimedean/boundary flux and put

```text
f_j(s)=F_j(s)-B_arch(s),       s in H_1.               (2)
```

Thus `f_j` is the candidate prime flux.  This definition uses the complete jet as a germ and
analytic continuation as a uniqueness constraint; it introduces no cutoff or propagated carrier.

## Canonical coefficient extraction

For a holomorphic function `f` on `H_1`, recursively define, whenever the limits exist,

```text
E_2(f) = lim_(x->+infinity) 2^x f(x),

E_N(f) = lim_(x->+infinity) N^x
           (f(x)-sum_(2<=n<N) E_n(f)n^(-x)),     N>=3.       (3)
```

Call `f` Dirichlet-admissible when every limit exists, the extracted stream

```text
c_f(N)=E_N(f)
```

belongs to

```text
A_>1={c : sum_(n>=2)|c_n|n^(-sigma)<infinity for every sigma>1},
```

and

```text
f(s)=sum_(n>=2)c_f(n)n^(-s)                             (4)
```

locally uniformly on `H_1`.

The extraction is canonical.  If (4) holds for some `c in A_>1`, then (3) recovers `c_N` for every
`N`.  Indeed, after the terms below `N` have been removed,

```text
N^x sum_(n>=N)c_n n^(-x)
  = c_N + sum_(n>N)c_n (N/n)^x.
```

Fix `sigma>1` at which the coefficient series is absolutely summable.  For `x>=sigma`, the tail is
dominated by

```text
N^sigma sum_(n>N)|c_n|n^(-sigma),
```

and every individual factor `(N/n)^(x-sigma)` tends to zero.  Dominated convergence gives the
required limit.  Induction on `N` proves the assertion.

Consequently no choice of coefficient representation enters the definition: an admissible
far-right function has exactly one extracted stream.

## Pure jet-space compatibility

Call the completed jet `j` Euler-compatible when:

1. its punctured germ (1) has the stated meromorphic continuation to `H_1`;
2. the prime part `f_j` from (2) is Dirichlet-admissible; and
3. its extracted coefficients satisfy

```text
c_f(n)=0                                             off prime powers,

c_f(p^m)c_f(p^n)=(log p)c_f(p^(m+n))                (5)
```

for every prime `p` and positive `m,n`.

Condition (5) is an all-order equation on the infinite jet: every `c_f(n)` is a canonical function
of the analytically continued jet through (1)--(4), so no auxiliary coefficient field remains in
the predicate.

## Exact image theorem

The following are equivalent:

```text
(i)  j is Euler-compatible;

(ii) there is a unique prime parameter field a : Primes -> C such that
     on H_1

     f_j(s)=sum_p sum_(m>=1) (log p)a_p^m p^(-ms),          (6)

     and the residue-filled continuation of
     f_j+B_arch has Taylor jet j at rho.
```

### Proof

Assume (ii).  Absolute convergence gives Dirichlet admissibility, and coefficient extraction gives

```text
c_f(p^m)=(log p)a_p^m,
c_f(n)=0 off prime powers.
```

These coefficients satisfy (5), so (i) follows.

Conversely, assume (i).  The exact coefficient-image theorem gives the unique parameters

```text
a_p=c_f(p)/(log p)
```

and reconstructs every coefficient as `(log p)a_p^m` on a prime-power ray.  Substitution in (4)
gives (6) on `H_1`.  Both sides are the same meromorphic continuation of the punctured germ (1), so
the identity theorem transports (6) back to the residue-filled germ at `rho`.  Uniqueness of `a`
is already read from the coefficient at `n=p`.  QED.

For the actual zeta source,

```text
c_f(n)=Lambda(n),
a_p=1 for every prime p.                               (7)
```

Thus (1)--(5), together with (7), classify the image of the fixed completed
prime--archimedean source inside infinite completed-flux jet space.

## Separation from arbitrary symmetric order-one realizers

The classifier is not a consequence of being entire of order one, FE-even, and Schwarz real.
For example, let `P(z)` be a nonconstant real even polynomial and put

```text
Q_epsilon(s)=1+epsilon P(s-1/2)
```

for a sufficiently small nonzero real `epsilon`.  Multiplying a completed symmetric order-one
realizer by `Q_epsilon` preserves order one, FE symmetry, and Schwarz reality.  Its completed flux
changes by

```text
-Q_epsilon'(s)/Q_epsilon(s).                           (8)
```

Along the positive real axis, (8) has only polynomial/rational decay, generically of order `1/s`.
Every Dirichlet-admissible prime flux instead satisfies

```text
f(x)=O(2^(-x))
```

after its first nonzero coefficient is isolated.  Hence `2^x f(x)` in (3) cannot have a finite
first extraction limit after the nonconstant gauge (8).  Such realizers fail the jet classifier.

More generally, if an arbitrary symmetric order-one realizer passes the classifier, its completed
logarithmic flux agrees on `H_1` with the completed degree-one Euler flux recovered in (6).  Equality
of logarithmic derivatives makes the two realizers constant multiples on every connected common
domain.  Therefore the classifier cuts out the completed Euler-source realizers, up to scalar
normalization, rather than the ambient symmetric order-one class.

## Topological boundary

This exact classifier is necessarily discontinuous in the compact-open topology of a strip germ.
The global fundamental-quadrant completeness theorem shows that finite Euler-unit gauges have dense
regular-flux orbit after the divisor is fixed, while (3)--(7) retain their weighted coefficient
tail.  Hence no continuous function of the infinite Taylor jet, or even of the complete regular
flux on the fundamental quadrant, can test Euler compatibility.

The two correct image statements are therefore simultaneous:

```text
arithmetic-at-infinity jet topology:
  (1)--(7) cut out the completed Euler source exactly;

compact-open strip topology:
  the same source orbit has full regular-flux closure after fixing the divisor.
```

## Scientific status and RH boundary

This theorem is `[BRIDGE]`, not new scientific knowledge.  Its ingredients are analytic
continuation uniqueness, ordinary Dirichlet coefficient extraction, and the rank-one geometric-ray
classification already formalized in `EulerSourceJetJacobian.lean`.  It completes the requested
set-theoretic image classification but introduces no new parent mechanism.

It also proves why source-image membership alone cannot imply RH.  Conditions (1)--(7) recover the
same fixed von Mangoldt source at every zeta zero, whether on or off the critical line.  The missing
scientific theorem must be a nonseparable compatibility of the pair

```text
(extracted weighted Euler tail, global symmetric divisor),
```

not a condition on either projection and not a continuous condition on the intervening regular
flux.  The candidate new completeness theorem supplies the significant negative boundary; this
card supplies the exact positive image classifier on the other side of that boundary.

## Formal interface

The current Lean tree already proves the algebraic and local analytic components:

- `completedFluxGermAt_eq_prime_add_archimedean_eventually`;
- `completedFluxTaylorCoeff_eq_prime_add_archimedean`;
- `degreeOneEulerQuadraticCompatible_iff_existsUnique_primeParameter`;
- `vonMangoldt_existsUnique_degreeOneEulerPrimeParameter`;
- `vonMangoldt_primeParameter_eq_one`.

The recursive limits (3), normal convergence (4), and analytic-continuation packaging are not yet
formalized.  They are not selected for isolated Lean work because the theorem is a classical bridge
and the remaining RH content begins only after this classifier.
