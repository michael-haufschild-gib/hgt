# Squared-Xi low-order complete monotonicity is unconditionally protected

- **ID:** squared-xi-low-order-complete-monotonicity-protected
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / RH-disproof route discriminator
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [SIGNIFICANT ROUTE KILL] [NOT FORMALIZED]`
- **Sources:** `XiEndpointStrongHeightGap.lean`; `PrimeArchScaledHausdorffDivisorValueRelation.lean`; the genus-zero canonical product of centered Xi in the squared variable; the critical-strip theorem
- **Statement:** For `y>1/4`, the squared-variable logarithmic derivative of centered Xi has the complete-monotonicity signs through derivative order thirteen, unconditionally.  Hence the first possible squared-seam derivative witness against RH has order at least fourteen.

## Theorem

Put

```text
g(y) = xi'(1/2+sqrt(y)) / (2*sqrt(y)*xi(1/2+sqrt(y)))
```

for `y>1/4`.  Then, for every integer `n` with `0<=n<=13`,

```text
(-1)^n g^(n)(y) > 0.                                      (1)
```

Equivalently, with `L(s)=xi'(s)/xi(s)` and
`F(w)=L(1/2+w)/w=2g(w^2)`, every alternating squared-coordinate derivative
of `F` through order thirteen has the RH-compatible strict sign on `w>1/2`.

In particular,

```text
w*L'(1/2+w)-L(1/2+w) < 0,                                (2)
```

so the first-gate inequality proposed in
`../../1-in-progress/absolute-euler-squared-seam-sign-violation.md` cannot
hold.

## Proof `[PROVED HERE]`

### 1. Uniform angle bound for every squared zero

Let `rho=sigma+i*gamma` be a nontrivial Xi zero and set

```text
delta = sigma-1/2,
t     = gamma^2-delta^2,
b     = 2*delta*gamma,
q     = b^2.
```

The critical strip gives `delta^2<=1/4`.  The already formalized endpoint
height theorem gives

```text
41/2 < gamma^2.                                           (3)
```

For `y>1/4`, put `A=y+t=y+gamma^2-delta^2`.  Then
`A>=gamma^2>0`, and hence

```text
x := q/A^2
   = 4*delta^2*gamma^2/A^2
   <= 1/gamma^2
   < 2/41.                                                (4)
```

The conjugate pair of squared zeros contributes a positive multiple of

```text
H(y) = A/(A^2+q) = Re(1/(A-i*b)).                         (5)
```

Critical-line zeros are the special case `b=0`.

### 2. Exact derivative signs through order six

For `k=n+1`, differentiation of (5) gives

```text
(-1)^n H^(n)(y)
  = n! * Re((A-i*b)^(-k)).                                (6)
```

After dividing by positive powers of `A` and `1+x`, the sign in (6) is the
sign of

```text
C_k(x) = Re((1-i*sqrt(x))^k).
```

For `1<=k<=7`, these polynomials are

```text
C_1 = 1,
C_2 = 1-x,
C_3 = 1-3x,
C_4 = 1-6x+x^2,
C_5 = 1-10x+5x^2,
C_6 = 1-15x+15x^2-x^3,
C_7 = 1-21x+35x^2-7x^3.                                  (7)
```

The first five are immediately positive for `0<=x<2/41` after discarding
their nonnegative final terms where appropriate.  For `C_6`,

```text
C_6(x) >= 1-15*(2/41)-(2/41)^3 > 0.                       (8)
```

For the last polynomial,

```text
C_7'(x) = -21+70x-21x^2 < -21+140/41 < 0
```

on `[0,2/41]`, while the exact endpoint value is

```text
C_7(2/41) = 4003/68921 > 0.                               (9)
```

Thus the height bound alone makes every orbit contribution in (6) have the
strict sign in (1) for `0<=n<=6`.

### 3. The formal reciprocal-square sector extends the protection

The current Lean corpus has a sharper input than the height estimate.  For
every Xi multiplicity copy, let

```text
lambda = xiZeroCopyReciprocalSquare = 1/(t-i*b).
```

`PrimeArchScaledHausdorffDivisorValueRelation.lean` proves pointwise that

```text
Re(lambda)>0,
(913/100)*|Im(lambda)| <= Re(lambda),                    (10)
```

and uses this sector to prove `Re(lambda^m)>=0` for every `1<=m<=14`.
For the shifted kernel in (5), put

```text
mu_y = 1/(t+y-i*b).
```

The imaginary-to-real ratios satisfy

```text
|Im(lambda)|/Re(lambda) = |b|/t,
|Im(mu_y)|/Re(mu_y)     = |b|/(t+y) <= |b|/t.            (11)
```

Thus `mu_y` lies in the same sector (10).  Equivalently,
`|arg(mu_y)|<=100/913`.  If `m<=14`, then

```text
|m*arg(mu_y)| <= 1400/913 < pi/2.                        (12)
```

The final rational inequality is already proved in the formal sector
argument.  Since `mu_y!=0`, equation (12) gives

```text
Re(mu_y^m)>0                                             (13)
```

for every `1<=m<=14`.  Combining (6) with `m=n+1` proves the per-orbit
strict derivative sign for every `0<=n<=13`.

### 4. Canonical-product assembly

The even entire function `w |-> xi(1/2+w)` is a genus-zero entire function
of order `1/2` in `y=w^2`.  Its logarithmic derivative is the absolutely and
locally normally convergent sum over squared zero orbits.  Therefore its
derivatives may be summed orbitwise on `y>1/4`.  Equations (10)--(13) make
every summand in (1) positive through order thirteen.  Xi has nontrivial
zeros, so the sum is strictly positive.  This proves (1).

Finally,

```text
d/dy [L(1/2+sqrt(y))/sqrt(y)]
  = [w*L'(1/2+w)-L(1/2+w)]/(2*w^3),
```

and (2) follows from the `n=1` case.  `QED`

## Sharpness of this discriminator

The height-only chamber proves positivity through derivative order six.  The
stronger formal reciprocal-square sector proves it through order thirteen.
That sector does not control the next power: its argument budget becomes
`1500/913`, which is larger than `pi/2`.  This does not produce a Xi witness;
it only shows that the first order not protected by the current exact sector
is derivative order fourteen.

## Consequence

Fixed orders `n=1,...,13` cannot disprove RH anywhere on the absolute Euler
ray `w>1/2`.  A surviving squared-seam attack must either:

1. prove the order-fourteen sign violation from the completed source;
2. use still higher order with a source-controlled order/base-point coupling;
3. leave the one-point complete-monotonicity test for a different exact
   RH-false witness.

## Gates

- [x] Existing formal height gap used instead of zero computation.
- [x] Every squared zero orbit placed in the exact chamber `x<2/41`.
- [x] Exact derivative polynomials through order seven proved positive.
- [x] Existing reciprocal-square sector transported to every shifted kernel.
- [x] Derivative protection extended through order thirteen.
- [x] Canonical-product assembly completed on paper.
- [ ] Independent audit of the squared-variable product normalization and differentiation.
- [ ] Lean formalization only if the protected-order theorem becomes a reused dependency.
