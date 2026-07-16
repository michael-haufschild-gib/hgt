# Von Mangoldt--Gamma affine boundary residual

- **ID:** `von-mangoldt-gamma-affine-boundary-residual`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), CUTOFF-COMPATIBLE TWO-BOUNDARY SOURCE PACKET
- **Scientific status:** `[PROVED] [FORMALIZED ALGEBRA] [PROVED ON PAPER CONVERGENCE FRONTIER]`
  `[BRIDGE] [NOT AN RH PROOF]`
- **Parents:**
  `von-mangoldt-gamma-all-depth-cauchy-gram.md`;
  `finite-von-mangoldt-gamma-full-jet-orientation.md`.

## Forced affine balance

The orthogonal two-boundary compression is positive at every finite aperture, but its projection
coefficients depend on that aperture.  This obstructs a direct cofinal limit.  The boundary
characters themselves force a compatible alternative.

For nonzero `a`, define

```text
c_+(a,w)=(a+w)/(2a),
c_-(a,w)=(a-w)/(2a),

B_a(w,lambda)
 =1/(lambda+w)
  -c_+(a,w)/(lambda+a)
  -c_-(a,w)/(lambda-a).                                 (1)
```

The coefficients are the unique affine coefficients which reproduce the constant and linear
functions of `w` at `w=+a,-a`.  Consequently

```text
B_a(+a,lambda)=B_a(-a,lambda)=0.                        (2)
```

Lean proves the exact factorization

```text
B_a(w,lambda)
 =(w^2-a^2)
   /((lambda+w)(lambda+a)(lambda-a)).                   (3)
```

Thus removing two boundary characters gains three inverse powers of the prime-log rate.  This is
not merely an orthogonal projection estimate; `(3)` is an exact source-cell identity.

## Source packet

Let

```text
A_(N,i)(w;n)
 =sqrt(Lambda(n)/n)
   *(log n)^i R_(N-i)(log n)/(w+log n)
```

be the formalized all-depth anomaly Cauchy feature.  Define

```text
A_aff(N,i,w;n)
 =A_(N,i)(w;n)
  -c_+(1/2,w)A_(N,i)(1/2;n)
  -c_-(1/2,w)A_(N,i)(-1/2;n).                           (4)
```

Lean proves

```text
A_aff(N,i,w;n)
 =sqrt(Lambda(n)/n)*(log n)^i R_(N-i)(log n)
   *(w^2-1/4)
    /((log n+w)(log n+1/2)(log n-1/2)).                 (5)
```

The finite vectors vanish identically at both boundary characters, their Grams are positive
semidefinite, and increasing the aperture preserves every existing coordinate exactly.  This last
prefix theorem is the gain over cutoff-dependent orthogonal projection.

## Cofinal depth frontier `[PROVED ON PAPER]`

On a fixed central compact set, for example `|w|<=1/4`, the denominators in `(5)` are uniformly
comparable to `(log n)^3` for `n>=2`.  At depth `N=2`, both jet numerators obey

```text
(log n)^i R_(2-i)(log n) <= log n,
i=0,1.                                                  (6)
```

Therefore

```text
|A_aff(2,i,w;n)|^2
 <= C * Lambda(n)/(n*(log n)^4)
 <= C /(n*(log n)^3),                                   (7)
```

using `Lambda(n)<=log n`.  The last series converges by the integral test.  Hence the depth-two
affine-balanced vectors have an actual `ell^2` Euler-boundary limit, their finite prefixes converge
strongly, and every finite packet Gram converges to a positive semidefinite limit.

Depth three also converges.  Its worst square is bounded by

```text
C*Lambda(n)/(n*(log n)^2).                              (8)
```

Partial summation with Chebyshev's unconditional bound `psi(x)<=C_0*x` gives convergence, since

```text
-d(1/(x*(log x)^2))
 =O(1/(x^2*(log x)^2)+1/(x^2*(log x)^3)).               (9)
```

For depth four the final jet coordinate has numerator asymptotic to `(log n)^3`, while `(3)`
contributes exactly `(log n)^(-3)`.  Away from `w=±1/2`, its squared feature is therefore
asymptotic to a nonzero multiple of `Lambda(n)/n`, whose sum diverges.  Higher depths are no
better.  Thus the two-boundary affine subtraction has the sharp source frontier

```text
cofinal ell^2 packet for N<=3;
no cofinal ell^2 packet from this subtraction alone for N>=4.          (10)
```

This kills the proposal that one fixed two-boundary compression can produce the complete Hankel
tower.  It positively salvages the first two- and three-jet discriminators.  Arbitrary degree
requires an order-growing boundary subtraction, a higher divided-difference packet, or the inverse
centered Green powers already isolated in the Hodge--Stieltjes route.

## RH impact

For the first `2 x 2` source packet, the convergence obstruction is no longer open: the explicit
affine-balanced source vectors possess a genuine positive Euler-boundary Gram limit.  The remaining
RH-bearing statement is the value identity

```text
limit Gram entries = m_0,m_1,m_2.                       (11)
```

The finite source construction, positivity, boundary cancellation, and convergence do not imply
`(11)`.  It must be derived from the causal/polar completed source formula and the inverse-tilted
central trace identity.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaAffineBoundaryBalance.lean`

Principal declarations:

- `twoBoundaryCauchyAffineResidual`
- `twoBoundaryCauchyAffineResidual_eq`
- `finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual`
- `finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_triple`
- `finiteVonMangoldtAllDepthAffineBalancedCauchyFeature`
- `finiteVonMangoldtAllDepthAffineBalancedCauchyVector_prefix`
- `finiteVonMangoldtAllDepthAffineBalancedCauchyGram_posSemidef`

## Gates

- [x] exact affine two-boundary coefficients
- [x] exact triple-denominator residual
- [x] both boundary values vanish
- [x] actual von Mangoldt/Gamma specialization
- [x] cutoff-prefix compatibility
- [x] finite Gram positivity
- [x] direct Lean check
- [x] no numerical computation
- [x] exact target build and axiom audit
- [ ] formalize depth-two and depth-three cofinal summability
- [ ] prove the depth-two completed moment-jet value identity `(11)`
- [ ] replace two-boundary balance by an arbitrary-order source construction
- [ ] RH
