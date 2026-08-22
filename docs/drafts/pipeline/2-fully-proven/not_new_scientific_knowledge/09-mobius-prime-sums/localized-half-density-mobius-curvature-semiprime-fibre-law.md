# Localized half-density Möbius curvature has exact semiprime product fibres

- **ID:** `localized-half-density-mobius-curvature-semiprime-fibre-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), POSITIVE SALVAGE
- **Scientific status:** `[PROVED HERE: LOCALIZATION] [BRIDGE] [PARENT THEORY]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parents:** `shifted-euler-quotient-finite-tangent-prime-support-filtration.md`,
  `shifted-euler-quotient-twisted-cocycle-flatness.md`,
  `prime-constraint-joining-dichotomy.md`, and `(35m20)`--`(35m22)` of
  `docs/reports/rh-proof-shape-1707.md`
- **Statement:** The symmetric half-density is the unique exponential normalization of the
  Möbius boundary germ whose second jet is the pure Dirichlet convolution square
  `Lambda*Lambda`.  Localizing that exactly flat germ by the triangular fixed-ratio kernel gives
  an exact endpoint-deletion formula.  Its ordinary semiprime product fibres contain precisely
  two ordered orientations, hence one real cosine mode and no internal cancellation; on the
  unclipped interior their sign changes at the sharp ratio threshold `c(1-c/A)`.

## 1. The half-density normalization is forced

For a real or complex parameter `sigma`, put

```text
b_sigma(n)=sum_(d|n)mu(d)d^(-sigma)
          =product_(p|n)(1-p^(-sigma)),

b_sigma^(a)(n)=n^(a sigma)b_sigma(n).                    (1)
```

Write `epsilon` for the Dirichlet-convolution unit and `*` for Dirichlet convolution.  At
`sigma=0`, coefficientwise differentiation gives

```text
b_0=epsilon,
b'_0=Lambda,
b''_0=Lambda*Lambda-Lambda log,                          (2)
```

where `(Lambda log)(n)=Lambda(n)log n` is a pointwise product.  Consequently

```text
(b^(a))'_0=Lambda,
(b^(a))''_0=Lambda*Lambda+(2a-1)Lambda log.              (3)
```

It follows that

```text
(b^(a))''_0=Lambda*Lambda for every n
                 if and only if a=1/2.                  (4)
```

The reverse implication is `(3)`.  For uniqueness, evaluate `(3)` at a prime `p`:
`(Lambda*Lambda)(p)=0`, whereas `Lambda(p)log p=(log p)^2` is nonzero.

Define the forced half-density coefficient

```text
e_sigma(n)=n^(sigma/2)product_(p|n)(1-p^(-sigma)).       (5)
```

On a common Euler half-plane,

```text
sum_n e_sigma(n)n^(-s)=zeta(s-sigma/2)/zeta(s+sigma/2).
```

Therefore

```text
e_sigma*e_(-sigma)=epsilon,                              (6)

e_0=epsilon,       e'_0=Lambda,       e''_0=Lambda*Lambda.
                                                                    (7)
```

Thus the factor `n^(sigma/2)` is not a cosmetic symmetrization.  It is the unique scalar
exponential twist that absorbs the `-Lambda log` leakage in the raw Möbius germ and makes the two
boundary directions exact convolution inverses.  With `sigma=2 omega`, `(5)` is exactly the
shifted Euler quotient coefficient already recorded in the parent cards.

### Proof of `(2)`

The Dirichlet series of `b_sigma` is `zeta(s)/zeta(s+sigma)`.  Its first derivative at zero is
`-zeta'/zeta`, whose coefficients are `Lambda`.  Its second derivative is

```text
(-zeta'/zeta)^2 + (-zeta'/zeta)',
```

whose coefficients are `Lambda*Lambda-Lambda log`.  All identities are also finite
coefficientwise identities, so no continuation or interchange of an infinite sum is needed for
the arithmetic statement.

## 2. Exact localized curvature and endpoint deletion

Let `W : R -> C` be even, let `R>1` be an integer, and for real `tau` define the finite product
fibre

```text
H_(R,W)(tau)
 =sum_(mn=R)e_(i tau)(m)e_(-i tau)(n)W(log(m/n)).        (8)
```

Also put

```text
L_W(R)=sum_(mn=R)Lambda(m)Lambda(n)W(log(m/n)).          (9)
```

Expanding `(7)` at `sigma=i tau` gives the exact boundary-curvature law

```text
1/2 H_(R,W)''(0)
 =L_W(R)-(Lambda*Lambda)(R)W(log R).                    (10)
```

The second term is the contribution of the two endpoint factorizations `(R,1)` and `(1,R)`.
For `W=1`, `(10)` is zero, as forced by the flat inverse law `(6)`.  Thus `(10)` is the exact
localized defect of all-grade convolution cancellation.

Now fix `0<c<A`, and put

```text
T_c(x)=(c-|x|)_+,
alpha=c^2/A,
K_(A,c)^int(x)=T_c(x)-alpha.                             (11)
```

If `log R>=c`, then `T_c(log R)=0`, so `(10)` becomes

```text
1/2 H_(R,T_c)''(0)=L_(T_c)(R).                          (12)
```

There is a stronger identity before differentiation.  Delete the two trivial factorization
endpoints and define

```text
J_(R,A,c)(tau)
 =sum_(mn=R; m,n>1)
    e_(i tau)(m)e_(-i tau)(n)K_(A,c)^int(log(m/n)).      (13)
```

Then `(6)` and `T_c(+-log R)=0` give

```text
J_(R,A,c)(tau)
 =H_(R,T_c)(tau)
  +alpha[e_(i tau)(R)+e_(-i tau)(R)].                   (14)
```

Indeed the sum of the nontrivial factor pairs in the constant kernel is the negative of the two
endpoint coefficients.  Differentiating `(14)` twice yields

```text
1/2 J_(R,A,c)''(0)
 =L_(T_c)(R)-alpha(Lambda*Lambda)(R)
 =L_(K_(A,c)^int)(R).                                   (15)
```

Equations `(14)`--`(15)` are the exact all-grade survivor.  The full inverse convolution makes
the constant centring disappear.  Matching the active fixed-ratio block, which excludes `1`,
forces it back as the explicit endpoint counterterm in `(14)`.

This counterterm is not a hidden positive measure.  Already for `R=pq`, `p!=q`,

```text
e_(i tau)(pq)+e_(-i tau)(pq)
 =-8 sin(tau log(p)/2) sin(tau log(q)/2),                (16)
```

which changes sign.  Near zero its curvature is exactly the negative semiprime centring required
by `(15)`.  Taking an absolute value or discarding it destroys the fixed-ratio cancellation.

## 3. Complete twisted product-fibre classification

For real `t`, define

```text
Lambda_t(n)=Lambda(n)n^(it),
C_t(R)=(Lambda_t*Lambda_(-t))(R).                        (17)
```

Because `Lambda` is supported on positive prime powers, unique factorization gives the complete
classification.

### At least three distinct prime divisors

If `R` has at least three distinct prime divisors, then

```text
C_t(R)=0.                                                (18)
```

No factorization `R=mn` can have both `m` and `n` positive prime powers.

### Two distinct prime divisors

If `R=p^a q^b`, where `p!=q` are prime and `a,b>=1`, then precisely two ordered
`Lambda`-supported factorizations survive, and

```text
C_t(p^a q^b)
 =2 log(p)log(q) cos(t(a log p-b log q)).                (19)
```

Thus a two-prime product fibre has ordered-pair cardinality two but only one real mode against an
even ratio kernel.  The two orientations reinforce; they cannot cancel each other.

### One prime divisor

If `R=p^k`, `k>=2`, then

```text
C_t(p^k)
 =(log p)^2 sum_(j=1)^(k-1) exp(i(2j-k)t log p)
 =(log p)^2 U_(k-2)(cos(t log p)),                       (20)
```

where `U_j` is the Chebyshev polynomial of the second kind.  For `R=1` or `R=p`, the coefficient
is zero.  The prime-power channel is already controlled at the required scale by `(35m15)`.

If an even kernel has a Fourier representation

```text
W(x)=integral W_hat(t)exp(itx)dt,
```

with a matching normalization, then

```text
L_W(R)=integral W_hat(t)C_t(R)dt.                        (21)
```

Equations `(18)`--`(20)` therefore give the exact spectral rank of every product layer.

## 4. Sharp semiprime sign chambers for the fixed-ratio kernel

For `R=p^a q^b` as above, set

```text
delta=a log p-b log q.
```

Equations `(11)` and `(19)` give

```text
L_(K_(A,c)^int)(p^a q^b)
 =2 log(p)log(q)[T_c(delta)-c^2/A].                      (22)
```

Since `0<c<A`, its sign is classified sharply by

```text
positive  iff |delta| < c(1-c/A),
zero      iff |delta| = c(1-c/A),
negative  iff |delta| > c(1-c/A).                       (23)
```

This includes the region `|delta|>=c`, where the triangular overlap vanishes and only the negative
centering remains.

For the exact fixed-ratio block of `(35m20a)`, ordinary distinct primes have `R=pq`.  The map from
an unordered pair `{p,q}` to `R=pq` is injective, and its complete product layer is

```text
2 log(p)log(q)/(pq) K_(A,c)(u_p,u_q),                   (24)
```

including the exact clipped kernel near the two aperture endpoints.  Formula `(23)` applies on
the unclipped interior.  Formula `(24)` shows, without an interior assumption, that grouping by
`R` is only a relabeling of the distinct-prime pair matrix: there is no intra-fibre averaging to
exploit.

## 5. Consequence for the open RH core

The strongest conclusion is structural, not an estimate:

> **Product-fibre rigidity.** After the controlled prime-power channel is removed, every
> unresolved ordinary-prime product fibre consists of one unordered pair, two reinforcing
> orientations, and one even cosine mode.  All cancellation capable of proving `(35m20d)` must
> occur across different products `R`, while retaining the aperture centring and the source
> weights.  Selberg or twisted-convolution regrouping cannot create cancellation inside a
> semiprime fibre.

The finite-tangent Gram remains nonnegative, but the target is a square-root-scale **upper** bound
on its curvature.  Positivity supplies only a lower bound.  A uniform finite-`tau` upper bound
strong enough to divide by `tau^2` is the missing estimate `(35m12)` or its RH-equivalent
fixed-ratio specialization `(35m20)`.  The endpoint counterterm `(14)` has no usable one-sided
sign, and the non-split Taylor remainder remains `(35m22)`.

Hence this theorem narrows the required new input to a cross-`R`, source-selected Type-II aperture
Stokes/covariance law.  It does not prove such a law.

## 6. Novelty and anti-theatre audit

This card is deliberately filed as **not new scientific knowledge**.

1. The half-density coefficient `(5)` is the existing shifted Euler quotient under
   `sigma=2 omega`.
2. The inverse law `(6)` is the flat twisted cocycle already recorded in the corpus.
3. The product-fibre classification `(18)`--`(20)` is unique factorization plus the classical
   prime-power support of `Lambda`.
4. The triangular kernel is the existing exact fixed-ratio kernel `(35m20b)`.
5. The endpoint-deletion identity `(14)` and sharp chamber `(23)` are useful new internal
   localizations of those parents, but they do not introduce an independent arithmetic estimate
   or invariant.

Calling `(15)` a positive curvature theorem would be theatre: the curvature is exactly the known
covariance, and the counterterm needed to retain centring is indefinite.  Calling `(19)` a new
bilinear estimate would also be theatre: it classifies one fibre but supplies no cancellation
between fibres.

## 7. Lean status

The unique-factorization core is already unconditional Lean code in
`formal/GaloisForLFunctions/HTGeometry/PrimeCollisionConvolution.lean`:

- `primePower_pair_orientation`;
- `equalPrimePower_pair_unordered`;
- `arithmeticOfPrimePowerColumn_mul_apply_distinct_unequal`;
- `arithmeticOfPrimePowerColumn_mul_apply_distinct_equal`.

The first half-density jet is already formalized as
`hasDerivAt_suzukiShiftedCoefficient` in
`formal/GaloisForLFunctions/RHTower/SuzukiCoupledErrorCriticalDerivative.lean`.

The exact new formalization target selected from this card is the finite second-jet and
endpoint-deletion package `(3)`--`(4)` and `(14)`--`(15)`.  It requires no asymptotics and no RH
hypothesis.  No new Lean file is claimed here: the shared one-process Lean slot was occupied when
this paper proof was completed.  The associated no-go must remain marked as formally unclosed
until that package receives an exact leaf build and axiom audit.

## Gates

- [x] half-density normalization and uniqueness proved
- [x] exact inverse convolution and localized boundary curvature proved
- [x] endpoint-deletion identity proved before differentiation
- [x] complete twisted product-fibre support and spectral classification proved
- [x] sharp interior semiprime sign chambers proved
- [x] RH/circularity and parent-theory audits passed
- [x] structural two-prime collision core located in existing verified Lean
- [ ] localized second-jet/endpoint-deletion package formalized and axiom-audited
- [ ] any cross-product source estimate stronger than the RH-equivalent covariance
